
#!/usr/bin/env python3
import os, time, json, threading, math
from datetime import datetime, timezone
from flask import Flask, render_template_string, request, jsonify, make_response
import requests, psycopg2, psycopg2.pool, psycopg2.extras
import xml.etree.ElementTree as ET

app = Flask(__name__)
DB_URL = os.environ.get("DATABASE_URL", "")
HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}

# ============ 绝对安全层（防御 AI 幻觉和脏数据） ============
def safe_float(val, default=0.0):
    if val is None: return default
    try: return float(val)
    except (ValueError, TypeError):
        try:
            import re
            m = re.search(r'-?\d+(\.\d+)?', str(val))
            return float(m.group()) if m else default
        except Exception:
            return default

def safe_int(val, default=0):
    return int(safe_float(val, default))

# ============ 全局缓存与状态 ============
_cache = {}
_long_term_cache = {"ts": 0, "wma_200": 0, "mayer": 0, "ahr999": 0, "bb_lower": 0, "bb_upper": 0}
_macro_cache = {"ts": 0, "data": {}}
_orderbook_cache = {"ts": 0, "data": None}
_whale_cache = {"ts": 0, "data": None}
_jin10_cache = {"ts": 0, "data": []}
_active_signal = {"data": None}
_ai_forecast = {"text": "AI 正在整合全维数据，进行前瞻预测...", "time": 0}

# 数据库状态与持仓快照
_db_alive = True
_pos_cache = []
_memory_settings = {} 

# 锁与熔断状态
_cache_lock, _strategy_lock, _log_lock = threading.Lock(), threading.Lock(), threading.Lock()
_api_penalty = {} 
_last_refresh = 0
_last_dying_warning = 0
_last_ai_patrol = 0
_last_breakout_check = 0
_last_breakout_price = 0
_updating_market = False

db_pool = psycopg2.pool.ThreadedConnectionPool(1, 10, DB_URL, sslmode='require') if DB_URL else None

SYSTEM_LOG = {k: {"status": "unknown", "msg": ""} for k in
    ["okx_kline","macro","news","derivatives","orderbook","whale","fng","deepseek","db","stablecoin"]}

def update_log(key, status, msg=""):
    with _log_lock:
        SYSTEM_LOG[key] = {"status": status, "msg": msg, "time": datetime.now().strftime("%H:%M:%S")}

def get_conn(): 
    global _db_alive
    if not db_pool: return None
    try:
        c = db_pool.getconn()
        if c.closed != 0:
            db_pool.putconn(c, close=True)
            c = db_pool.getconn()
        _db_alive = True
        return c
    except Exception:
        _db_alive = False
        return None

def release_conn(c):
    if db_pool and c:
        try: c.rollback()
        except Exception: pass
        db_pool.putconn(c)

def init_db():
    c = get_conn()
    if not c: return
    try:
        cur = c.cursor()
        cur.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT)")
        cur.execute("""CREATE TABLE IF NOT EXISTS positions (id SERIAL PRIMARY KEY, entry_price REAL, quantity REAL, entry_usdt REAL, status TEXT DEFAULT 'open', opened_at TEXT, tp1_price REAL, tp1_hit BOOLEAN DEFAULT false, tp2_price REAL, tp2_hit BOOLEAN DEFAULT false, tp3_price REAL, tp3_hit BOOLEAN DEFAULT false, stop_loss_price REAL, sl_hit BOOLEAN DEFAULT false, tp_metadata TEXT DEFAULT '{}', remaining_qty REAL DEFAULT 0, realized_pnl REAL DEFAULT 0, is_long_term BOOLEAN DEFAULT false)""")
        cur.execute("ALTER TABLE positions ADD COLUMN IF NOT EXISTS is_long_term BOOLEAN DEFAULT false")
        c.commit()
    except Exception as e:
        try: c.rollback()
        except: pass
        update_log("db", "error", str(e))
    finally: release_conn(c)

def db_health_worker():
    global _db_alive
    while True:
        time.sleep(30)
        if not db_pool: continue
        try:
            c = db_pool.getconn()
            cur = c.cursor()
            cur.execute("SELECT 1")
            c.commit()
            db_pool.putconn(c)
            if not _db_alive:
                _db_alive = True
                update_log("db", "ok", "数据库已恢复")
                push_feishu("✅ 数据库已恢复", "Supabase 维护/网络波动已结束，系统重新开启仓位记录功能。")
                try: init_db()
                except: pass
        except Exception:
            if _db_alive:
                _db_alive = False
                update_log("db", "error", "数据库断开")
                push_feishu("🚨 数据库断开告警", "Supabase 连不上了。行情正常，仓位记录已暂停。恢复后自动通知。")

# ============ 数据抓取模块 ============
def get_setting(k, d=None):
    if k in _memory_settings:
        return _memory_settings[k]
    defaults = {"total_capital": "10000", "target_capital": "20000", "account_btc": "0",
        "account_usdt": "0", "reserve_ratio": "0.5", "short_term_amount": "500",
        "min_win_rate": "60", "feishu_webhook": "", "deepseek_key": "", "siliconflow_key": "",
        "bs_tier": "0", "ai_patrol_minutes": "60"}
    c = get_conn()
    if not c: return defaults.get(k, d)
    try:
        cur = c.cursor(); cur.execute("SELECT value FROM settings WHERE key=%s", (k,))
        r = cur.fetchone()
        val = r[0] if r else defaults.get(k, d)
        if val is not None: _memory_settings[k] = val
        return val
    except Exception: return defaults.get(k, d)
    finally: release_conn(c)

def set_setting(k, v):
    _memory_settings[k] = str(v)
    c = get_conn()
    if not c: return
    try:
        cur = c.cursor()
        cur.execute("INSERT INTO settings (key, value) VALUES (%s, %s) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value", (k, str(v)))
        c.commit()
    except Exception:
        try: c.rollback()
        except: pass
    finally: release_conn(c)

def get_int_setting(k, default):
    try: return int(float(get_setting(k, str(default))))
    except (ValueError, TypeError): return default

def get_klines(bar="4H", limit=200):
    global _api_penalty
    bar_map_bin = {"4H": "4h", "1D": "1d", "1W": "1w", "1H": "1h"}
    bar_map_okx = {"4H": "4H", "1D": "1Dutc", "1W": "1Wutc", "1H": "1H"}
    bar_map_bybit = {"4H": "240", "1D": "D", "1W": "W", "1H": "60"}
    
    if time.time() > _api_penalty.get("bin_k", 0):
        try:
            r = requests.get(f"https://data-api.binance.vision/api/v3/klines?symbol=BTCUSDT&interval={bar_map_bin.get(bar, bar)}&limit={limit}", headers=HEADERS, timeout=4)
            if r.status_code == 200 and r.text.startswith("["):
                bin_data = r.json()
                if len(bin_data) >= 100:
                    update_log("okx_kline", "ok", "币安正常(主)")
                    return [[str(k[0]), str(k[1]), str(k[2]), str(k[3]), str(k[4]), str(k[5])] for k in bin_data][:-1]
            elif r.status_code in [429, 500, 502, 503, 504]:
                _api_penalty["bin_k"] = time.time() + 60
        except Exception: _api_penalty["bin_k"] = time.time() + 60
            
    if time.time() > _api_penalty.get("okx_k", 0):
        try:
            r = requests.get("https://www.okx.com/api/v5/market/candles";, params={"instId": "BTC-USDT", "bar": bar_map_okx.get(bar, bar), "limit": limit}, headers=HEADERS, timeout=4)
            if r.status_code == 200 and r.text.startswith("{"):
                data = r.json().get("data", [])
                if len(data) >= 100:
                    update_log("okx_kline", "backup", "已切OKX")
                    data.reverse() 
                    return data[:-1]
            else: _api_penalty["okx_k"] = time.time() + 60
        except Exception: _api_penalty["okx_k"] = time.time() + 60

    if time.time() > _api_penalty.get("bybit_k", 0):
        try:
            r = requests.get(f"https://api.bybit.com/v5/market/kline?category=spot&symbol=BTCUSDT&interval={bar_map_bybit.get(bar, bar)}&limit={limit}", headers=HEADERS, timeout=4)
            if r.status_code == 200 and r.text.startswith("{"):
                bybit_data = r.json().get("result", {}).get("list", [])
                if len(bybit_data) >= 100:
                    update_log("okx_kline", "backup", "已切Bybit")
                    bybit_data.reverse()
                    return [[str(k[0]), str(k[1]), str(k[2]), str(k[3]), str(k[4]), str(k[5])] for k in bybit_data][:-1]
            else: _api_penalty["bybit_k"] = time.time() + 60
        except Exception: _api_penalty["bybit_k"] = time.time() + 60

    update_log("okx_kline", "error", "全源K线超时")
    return []

def get_realtime_price():
    try:
        r = requests.get("https://data-api.binance.vision/api/v3/ticker/price?symbol=BTCUSDT";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"): 
            p = safe_float(r.json().get("price"))
            if p > 0: return p
    except Exception: pass
    try:
        r = requests.get("https://api-gcp.binance.com/api/v3/ticker/price?symbol=BTCUSDT";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"): 
            p = safe_float(r.json().get("price"))
            if p > 0: return p
    except Exception: pass
    try:
        r = requests.get("https://www.okx.com/api/v5/market/ticker?instId=BTC-USDT";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"): 
            p = safe_float(r.json()["data"][0].get("last"))
            if p > 0: return p
    except Exception: pass
    return 0.0

def get_order_book():
    global _orderbook_cache, _api_penalty
    if time.time() - _orderbook_cache["ts"] < 180 and _orderbook_cache["data"]: return _orderbook_cache["data"]
    res = {"buy_vol": 0, "sell_vol": 0, "ratio": 1.0, "text": "盘口中性"}
    bids, asks = [], []
    if time.time() > _api_penalty.get("bin_ob", 0):
        try:
            r = requests.get("https://data-api.binance.vision/api/v3/depth?symbol=BTCUSDT&limit=20";, headers=HEADERS, timeout=2.5)
            if r.status_code == 200 and r.text.startswith("{"):
                data = r.json()
                bids = data.get("bids", []); asks = data.get("asks", [])
                update_log("orderbook", "ok", "币安盘口(主)")
            else: _api_penalty["bin_ob"] = time.time() + 60
        except Exception: _api_penalty["bin_ob"] = time.time() + 60
    
    if not bids:
        try:
            r = requests.get("https://www.okx.com/api/v5/market/books";, params={"instId": "BTC-USDT", "sz": 20}, headers=HEADERS, timeout=2.5)
            if r.status_code == 200 and r.text.startswith("{"):
                data = r.json().get("data", [])
                if data and len(data) >= 1:
                    bids = data[0][:20]; asks = data[1][:20]
                    update_log("orderbook", "backup", "已切OKX")
        except Exception: pass

    if bids and asks:
        bv = sum([safe_float(b[1]) for b in bids]); sv = sum([safe_float(a[1]) for a in asks])
        ratio = bv / sv if sv > 0 else 1.0
        res = {"buy_vol": round(bv, 2), "sell_vol": round(sv, 2), "ratio": round(ratio, 2)}
        if ratio > 1.5: res["text"] = "买盘极强(托底)"
        elif ratio < 0.67: res["text"] = "卖盘极强(抛压)"
        else: res["text"] = "买卖均衡"
        _orderbook_cache = {"ts": time.time(), "data": res}
        return res
    return res

def get_whale_activity():
    global _whale_cache
    if time.time() - _whale_cache["ts"] < 300 and _whale_cache["data"]: return _whale_cache["data"]
    try:
        r = requests.get("https://coinlobster.com/mcp/whale_radar";, params={"symbol": "BTC"}, headers=HEADERS, timeout=2.5)
        if r.status_code == 200 and r.text.startswith("{"):
            data = r.json(); nf = safe_float(data.get("net_flow_24h", 0))
            if nf > 1000: res = {"action": "买入", "text": f"巨鲸大幅净流入 {nf} BTC"}
            elif nf < -1000: res = {"action": "卖出", "text": f"巨鲸大幅净流出 {nf} BTC"}
            else: res = {"action": "中性", "text": "巨鲸资金平稳"}
            update_log("whale", "ok", "巨鲸正常")
            _whale_cache = {"ts": time.time(), "data": res}
            return res
    except Exception: pass
    return {"action": "未知", "text": "巨鲸数据暂不可用(已跳过)"}

def get_macro_ext():
    global _macro_cache
    if time.time() - _macro_cache["ts"] < 3600 and _macro_cache["data"]: return _macro_cache["data"]
    res = {"spx": "未知", "dxy": "未知", "vix": "未知", "xau": "未知", "text": "宏观中性"}
    
    def parse_stooq(ticker, key):
        try:
            r = requests.get(f"https://stooq.com/q/l/?s={ticker}&f=sd2t2ohlcv&h&e=csv", headers=HEADERS, timeout=3)
            if r.status_code == 200:
                lines = r.text.strip().split("\n")
                if len(lines) >= 2:
                    parts = lines[1].split(",")
                    if len(parts) >= 7:
                        val = safe_float(parts[6])
                        if val > 0: res[key] = round(val, 2)
        except Exception: pass

    parse_stooq("^spx", "spx")
    parse_stooq("dx.f", "dxy")
    parse_stooq("vix", "vix")
    parse_stooq("xauusd", "xau")

    if res["dxy"] != "未知" and res["vix"] != "未知": 
        res["text"] = f"SPX:{res['spx']} 黄金:{res['xau']} DXY:{res['dxy']} VIX:{res['vix']}"
    _macro_cache = {"ts": time.time(), "data": res}
    return res

def get_jin10_news():
    global _jin10_cache
    if time.time() - _jin10_cache["ts"] < 600 and _jin10_cache["data"]: return _jin10_cache["data"]
    news_list = []
    keywords = ["美联储", "非农", "CPI", "ETF", "降息", "加息", "鲍威尔", "SEC", "通胀"]
    try:
        url = "https://flash-api.jin10.com/get_flash_list?channel=-8200&vip=1";
        headers = {"User-Agent": "Mozilla/5.0", "x-app-id": "bVBF4FyRTn5NJF5n", "x-version": "1.0.0"}
        r = requests.get(url, headers=headers, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"):
            for item in r.json().get("data", []):
                if not item.get("data"): continue
                content = item["data"].get("content", "")
                imp = safe_int(item.get("importance", 1))
                if imp >= 2 or any(k in content for k in keywords):
                    clean = content.replace("\n", " ").strip()
                    if len(clean) > 10: news_list.append(f"{'🔴' if imp>=2 else '🟡'} {clean[:60]}")
                if len(news_list) >= 5: break
            update_log("news", "ok", "金十抓取成功")
    except Exception: pass
    if not news_list:
        try:
            r = requests.get("https://www.coindesk.com/arc/outboundfeeds/rss/";, headers=HEADERS, timeout=3)
            if r.status_code == 200 and r.text.startswith("<?xml"):
                items = ET.fromstring(r.content).findall(".//item")[:3]
                news_list = [f"🟡 {item.find('title').text}" for item in items]
                update_log("news", "backup", "已切CoinDesk")
        except Exception: update_log("news", "skip", "新闻全挂")
    _jin10_cache = {"ts": time.time(), "data": news_list}
    return news_list

def get_btc_dominance():
    try:
        r = requests.get("https://api.coingecko.com/api/v3/global";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"):
            data = r.json().get("data", {})
            return safe_float(data["market_cap_percentage"]["btc"], 50.0)
    except Exception: pass
    try:
        r = requests.get("https://api.coinlore.net/api/global/";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("["): return safe_float(r.json()[0].get("btc_d"), 50.0)
    except Exception: pass
    return 50.0

def get_stablecoin_premium():
    try:
        r1 = requests.get("https://api.coinbase.com/v2/prices/USDT-USD/spot";, headers=HEADERS, timeout=3)
        if r1.status_code == 200 and r1.text.startswith("{"):
            usdt_usd = safe_float(r1.json()["data"].get("amount"), 1.0)
            prem = round((usdt_usd - 1) * 100, 3)
            text = "溢价均衡"
            if prem > 0.15: text = "正溢价(场外资金进场)"
            elif prem < -0.15: text = "负溢价(资金出逃)"
            update_log("stablecoin", "ok", "溢价正常")
            return {"premium": prem, "text": text}
    except Exception: pass
    update_log("stablecoin", "skip", "溢价获取失败")
    return {"premium": 0.0, "text": "溢价未知"}

def get_derivatives_risk():
    res = {"oi": 0, "long_short_ratio": 1.0, "liq_text": "杠杆均衡"}
    try:
        r = requests.get("https://fapi.binance.com/fapi/v1/openInterest?symbol=BTCUSDT";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("{"): 
            res["oi"] = round(safe_float(r.json().get("openInterest")), 2)
    except Exception: pass
        
    try:
        r = requests.get("https://fapi.binance.com/futures/data/globalLongShortAccountRatio?symbol=BTCUSDT&period=4h&limit=1";, headers=HEADERS, timeout=3)
        if r.status_code == 200 and r.text.startswith("["):
            j = r.json()
            if len(j) > 0: res["long_short_ratio"] = round(safe_float(j[0].get("longShortRatio"), 1.0), 2)
    except Exception: pass
    
    if res["long_short_ratio"] > 2.0: res["liq_text"] = "散户极度看多(警惕爆多单)"
    elif res["long_short_ratio"] < 0.5: res["liq_text"] = "散户极度看空(警惕逼空)"
    else: res["liq_text"] = f"多空比 {res['long_short_ratio']}"
    return res

def calc_atr_macd(klines):
    if len(klines) < 30: return 0, 0
    try:
        closes = [safe_float(k[4]) for k in klines]
        highs = [safe_float(k[2]) for k in klines]
        lows = [safe_float(k[3]) for k in klines]
        trs = []
        for i in range(1, len(closes)):
            tr = max(highs[i] - lows[i], abs(highs[i] - closes[i-1]), abs(lows[i] - closes[i-1]))
            trs.append(tr)
        atr = round(sum(trs[-14:]) / 14, 2) if len(trs) >= 14 else 0
        ema12 = sum(closes[-12:]) / 12
        ema26 = sum(closes[-26:]) / 26
        macd = round(ema12 - ema26, 2)
        return atr, macd
    except Exception:
        return 0, 0

def check_multi_timeframe_trend(ks_4h, ks_1d):
    try:
        k1h = get_klines("1H", 50)
        t1h = t4h = t1d = "空"
        if len(k1h)>20 and safe_float(k1h[-1][4]) > sum([safe_float(k[4]) for k in k1h[-20:]])/20: t1h = "多"
        if len(ks_4h)>20 and safe_float(ks_4h[-1][4]) > sum([safe_float(k[4]) for k in ks_4h[-20:]])/20: t4h = "多"
        if len(ks_1d)>20 and safe_float(ks_1d[-1][4]) > sum([safe_float(k[4]) for k in ks_1d[-20:]])/20: t1d = "多"
        return f"1H:{t1h} | 4H:{t4h} | 1D:{t1d}"
    except Exception:
        return "获取失败"

def get_advance_metrics(dks):
    global _long_term_cache, _api_penalty
    metrics = {"wma_200": 0, "mayer": 0, "ahr999": 0, "funding": 0, "funding_text": "中性", 
               "bb_lower": 0, "bb_upper": 0, "ob_ratio": 1.0, "ob_text": "中性", "whale_action": "未知", "whale_text": ""}
               
    if time.time() - _long_term_cache["ts"] > 3600:
        try:
            wks = get_klines("1W", 200)
            if len(wks) >= 199: _long_term_cache["wma_200"] = sum([safe_float(k[4]) for k in wks]) / 200
            if dks and len(dks) >= 199:
                closes = [safe_float(k[4]) for k in dks]
                ma200 = sum(closes) / 200; c = closes[-1]
                _long_term_cache["mayer"] = round(c / ma200, 2) if ma200 > 0 else 0
                days = (datetime.now(timezone.utc) - datetime(2009, 1, 3, tzinfo=timezone.utc)).days
                exp_g = 10 ** (2.66167155 * math.log10(days) - 17.918)
                _long_term_cache["ahr999"] = round((c / ma200) * (c / exp_g), 3) if ma200 > 0 and exp_g > 0 else 0
                r20 = closes[-20:]; sma20 = sum(r20) / 20
                std20 = (sum([(x - sma20)**2 for x in r20]) / 20) ** 0.5
                _long_term_cache["bb_upper"] = round(sma20 + 2 * std20, 2)
                _long_term_cache["bb_lower"] = round(sma20 - 2 * std20, 2)
        except Exception: pass
        _long_term_cache["ts"] = time.time()

    metrics.update({k: _long_term_cache[k] for k in ["wma_200", "mayer", "ahr999", "bb_upper", "bb_lower"]})

    funding_success = False
    if time.time() > _api_penalty.get("bin_fr", 0):
        try:
            r = requests.get("https://fapi.binance.com/fapi/v1/premiumIndex?symbol=BTCUSDT";, headers=HEADERS, timeout=3)
            if r.status_code == 200 and r.text.startswith("{"):
                metrics["funding"] = round(safe_float(r.json().get("lastFundingRate")) * 100, 4)
                funding_success = True
            else: _api_penalty["bin_fr"] = time.time() + 60
        except Exception: _api_penalty["bin_fr"] = time.time() + 60

    if not funding_success:
        try:
            r = requests.get("https://www.okx.com/api/v5/public/funding-rate?instId=BTC-USDT-SWAP";, headers=HEADERS, timeout=3)
            if r.status_code == 200 and r.text.startswith("{"):
                metrics["funding"] = round(safe_float(r.json()["data"][0].get("fundingRate")) * 100, 4)
                update_log("derivatives", "backup", "费率切OKX")
        except Exception: pass
        
    if metrics["funding"] > 0.05: metrics["funding_text"] = "多头过热"
    elif metrics["funding"] < -0.05: metrics["funding_text"] = "空头拥挤"

    ob = get_order_book(); metrics["ob_ratio"] = ob["ratio"]; metrics["ob_text"] = ob["text"]
    whale = get_whale_activity(); metrics["whale_action"] = whale["action"]; metrics["whale_text"] = whale["text"]
    return metrics

def ask_ai(p):
    k = get_setting("deepseek_key")
    if k:
        try:
            res = requests.post("https://api.deepseek.com/chat/completions";,
                headers={"Authorization": f"Bearer {k}"},
                json={"model": "deepseek-chat", "messages": [{"role": "user", "content": p}]}, timeout=20)
            if res.status_code == 200 and res.text.startswith("{"):
                update_log("deepseek", "ok", "DeepSeek正常")
                return res.json()["choices"][0]["message"]["content"]
        except Exception: pass
    
    sk = get_setting("siliconflow_key")
    if sk:
        try:
            res = requests.post("https://api.siliconflow.cn/v1/chat/completions";,
                headers={"Authorization": f"Bearer {sk}"},
                json={"model": "Qwen/Qwen2.5-7B-Instruct", "messages": [{"role": "user", "content": p}]}, timeout=20)
            if res.status_code == 200 and res.text.startswith("{"):
                update_log("deepseek", "backup", "已切备选AI")
                return res.json()["choices"][0]["message"]["content"]
        except Exception: pass
    update_log("deepseek", "skip", "AI全挂")
    return None

def push_feishu(t, c):
    url = get_setting("feishu_webhook")
    if url and url.startswith("https://open.feishu.cn/";):
        try: requests.post(url, json={"msg_type": "text", "content": {"text": f"🔔【{t}】\n\n{c}"}}, timeout=5)
        except Exception: pass

def get_market():
    global _updating_market
    with _cache_lock:
        if "main" in _cache and time.time() - _cache["main"]["ts"] < 300:
            return _cache["main"]["data"]
        if _updating_market:
            if "main" in _cache: return _cache["main"]["data"]
            return {"error": "数据正在加载中，请稍后再试"}
        _updating_market = True

    try:
        ks = get_klines("4H", 200)
        if not ks or len(ks) < 199:
            global _last_dying_warning
            if time.time() - _last_dying_warning > 3600:
                push_feishu("🚨 系统濒死告警", "所有交易所K线接口全部断连！请立刻打开币安App查看！")
                _last_dying_warning = time.time()
            with _cache_lock:
                if "main" in _cache: return _cache["main"]["data"]
            return {"error": "核心K线数据全源失败"}

        cur = get_realtime_price()
        if cur == 0: cur = safe_float(ks[-1][4])
        
        closes = [safe_float(k[4]) for k in ks]
        gains = [max(closes[i] - closes[i-1], 0) for i in range(1, len(closes))]
        losses = [max(closes[i-1] - closes[i], 0) for i in range(1, len(closes))]
        ag, al = sum(gains[-14:])/14, sum(losses[-14:])/14
        rsi = round(100 - 100/(1 + ag/al), 2) if al > 0 else 100.0
        
        dks = get_klines("1D", 200)
        if dks and len(dks) >= 199:
            rh = max([safe_float(k[2]) for k in dks])
        else:
            rh = max([safe_float(k[2]) for k in ks])
        dd = (rh - cur) / rh * 100 if rh > 0 else 0
        
        fng = 50
        try: 
            r = requests.get("https://api.alternative.me/fng/?limit=1";, timeout=3)
            if r.status_code == 200 and r.text.startswith("{"): fng = safe_int(r.json()["data"][0].get("value"), 50)
        except Exception: pass

        adv = get_advance_metrics(dks)
        mac_ext = get_macro_ext()
        news = get_jin10_news()
        dom = get_btc_dominance()
        deriv = get_derivatives_risk()
        atr, macd = calc_atr_macd(ks)
        premium = get_stablecoin_premium()
        mtf = check_multi_timeframe_trend(ks, dks)
        
        ahr_s = min(100, max(0, (1.2 - adv["ahr999"]) / 1.2 * 100)) if adv["ahr999"] > 0 else 50
        mayer_s = min(100, max(0, (1.5 - adv["mayer"]) / 1.0 * 100)) if adv["mayer"] > 0 else 50
        val_score = int((ahr_s * 0.4) + (mayer_s * 0.4) + (fng * 0.2))

        detail_html = f"""
        <div style="font-size:13px; line-height:1.8; color:#EAECEF;">
        <b>📊 周期与估值</b><br>
        • 综合估值评分：{val_score}/100<br>
        • AHR999：{adv['ahr999']} / Mayer：{adv['mayer']}<br>
        • 200周均线：${round(adv['wma_200'],2)}<br>
        • 布林带区间：${adv['bb_lower']} - ${adv['bb_upper']}<br>
        <br>
        <b>⚙️ 技术面与衍生品</b><br>
        • 多周期趋势：{mtf}<br>
        • MACD(4H)：{macd} / ATR(14)：{atr}<br>
        • 资金费率：{adv['funding']}% ({adv['funding_text']})<br>
        • 盘口深度：{adv['ob_text']}<br>
        • {deriv['liq_text']} (OI:{deriv['oi']})<br>
        • BTC市值占比：{dom}%<br>
        <br>
        <b>🌍 宏观与资金面</b><br>
        • 稳定币溢价：{premium['premium']}% ({premium['text']})<br>
        • 跨市场联动：{mac_ext['text']}<br>
        • 恐慌贪婪：{fng}<br>
        • 巨鲸动向：{adv['whale_text']}<br>
        <br>
        <b>📰 最新快讯</b><br>
        """ + "".join([f"• {n}<br>" for n in news])

        sig = _active_signal["data"]
        if sig and time.time() > sig["time"] + sig["ttl"]:
            _active_signal["data"] = None; sig = None

        data = {
            "current": cur, "rsi": rsi, "fng": fng, "val_score": val_score, "drawdown": round(dd, 2),
            "verdict": _ai_forecast["text"], "macro_text": mac_ext["text"],
            "trend": "多头" if cur > sum(closes[-20:])/20 else "空头",
            "detail": detail_html, "logs": SYSTEM_LOG, "active_signal": sig,
            "news_str": " | ".join(news[:3]), "recent_high": rh,
            "funding": adv["funding"], "ob_text": adv["ob_text"], "whale_text": adv["whale_text"],
            "deriv_text": deriv["liq_text"], "premium_text": premium["text"], "mtf": mtf,
            "db_alive": _db_alive
        }
        with _cache_lock:
            _cache["main"] = {"data": data, "ts": time.time()}
        return data
    finally:
        with _cache_lock:
            _updating_market = False

# ============ AI 巡检与策略 ============
def ai_patrol_worker(d):
    global _ai_forecast, _active_signal
    try:
        cur = d["current"]
        c = get_conn(); positions = []
        if c:
            try:
                cur_db = c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
                cur_db.execute("SELECT * FROM positions WHERE status='open' ORDER BY id ASC")
                positions = cur_db.fetchall()
            except Exception: pass
            finally: release_conn(c)

        pos_str = "无持仓"
        if positions:
            pos_str = ""
            for p in positions:
                entry = safe_float(p.get("entry_price"))
                if entry <= 0: continue
                entry_usdt = safe_float(p.get("entry_usdt"))
                pnl = (cur - entry) / entry * 100
                is_long = p.get("is_long_term", False)
                pos_str += f"仓位#{p['id']}: 成本{entry}, 买入金额{entry_usdt}U, 浮盈亏{pnl:.2f}%。{'【长线防守，禁提止损】' if is_long else ''}\n"

        prompt = f"""你现在是极其顶级的量化交易主脑。结合【全维度全景数据】给出前瞻预测。
    【全景数据】
    - 现价:{cur} RSI:{d['rsi']} 恐慌贪婪:{d['fng']} 估值评分:{d['val_score']}/100
    - 宏观:{d['macro_text']} 费率:{d.get('funding','未知')} 稳定币溢价:{d.get('premium_text','未知')}
    - 盘口:{d.get('ob_text','未知')} 巨鲸:{d.get('whale_text','未知')} 衍生品:{d.get('deriv_text','未知')}
    - 多周期趋势:{d.get('mtf','未知')}
    - 新闻:{d.get('news_str','')}
    - 持仓:{pos_str}

    请严格输出JSON（不要多余文字）：
    {{
        "forecast_text": "结合全盘信息，预计未来1-3天走势是...（大白话，50字内，指出当前更合适左侧限价等接还是右侧市价追）",
        "is_buy_signal": true/false,
        "buy_plan": {{ 
            "entry_low": 数字, "entry_high": 数字, "win_rate": 数字, "days": 数字,
            "reason": "左侧限价理由", "market_trigger": 数字, "market_win_rate": 数字,
            "market_reason": "右侧市价突破理由"
        }},
        "position_updates": [
            {{ "id": 仓位ID, "action": "hold/stop_loss/wait_rebound", "win_rate": 数字, "days": 数字, "reason": "理由", "new_tp1": 数字或null, "new_tp2": 数字或null, "new_tp3": 数字或null, "new_stop_loss": 数字或null }}
        ]
    }}"""
        rep = ask_ai(prompt)
        if not rep: return
        ai_res = json.loads(rep.replace("```json", "").replace("```", "").strip())
        
        if ai_res.get("forecast_text"):
            _ai_forecast["text"] = ai_res["forecast_text"]; _ai_forecast["time"] = time.time()

        if ai_res.get("is_buy_signal") and ai_res.get("buy_plan"):
            plan = ai_res["buy_plan"]; min_wr = get_int_setting("min_win_rate", 60)
            pw = safe_float(plan.get("win_rate")); mw = safe_float(plan.get("market_win_rate"))
            e_low = safe_float(plan.get("entry_low")); e_high = safe_float(plan.get("entry_high"))
            if (pw >= min_wr or mw >= min_wr) and e_low > 0 and e_high > e_low:
                pm = get_int_setting("ai_patrol_minutes", 60)
                ttl_sec = (pm * 60) if pm > 0 else 3600
                with _cache_lock:
                    _active_signal["data"] = {
                        "type": "buy", "entry_low": e_low, "entry_high": e_high,
                        "win_rate": int(pw), "days": safe_int(plan.get("days"), 3), "market_trigger": safe_float(plan.get("market_trigger")),
                        "market_win_rate": int(mw), "market_reason": plan.get("market_reason"),
                        "time": time.time(), "ttl": ttl_sec
                    }
                push_feishu("🔥 AI 发现交易机会", f"左侧限价: {e_low} - {e_high}\n右侧触发: 突破 {plan.get('market_trigger')}\n胜率: {pw}% / 预计{safe_int(plan.get('days'), 3)}天")

        if ai_res.get("position_updates"):
            c2 = get_conn()
            if c2:
                try:
                    cur2 = c2.cursor()
                    for up in ai_res["position_updates"]:
                        pid = safe_int(up.get("id"))
                        if not pid: continue
                        action = up.get("action", "hold")
                        cur2.execute("SELECT is_long_term FROM positions WHERE id=%s", (pid,))
                        row = cur2.fetchone(); is_long = row[0] if row else False
                        if is_long and action == "stop_loss":
                            action = "hold"; up["reason"] = "（长线模式，忽略止损）" + (up.get("reason") or "")
                        if action in ["stop_loss", "wait_rebound"]:
                            title = "🔴 建议止损" if action == "stop_loss" else "🟡 等反弹"
                            push_feishu(f"🚨 [仓位#{pid}] 预警", f"AI 诊断: {title}\n胜率:{up.get('win_rate','--')}%\n预计:{up.get('days','--')}天\n理由: {up.get('reason','无')}")
                        
                        t_tp1 = safe_float(up.get("new_tp1"))
                        t_tp2 = safe_float(up.get("new_tp2"))
                        t_tp3 = safe_float(up.get("new_tp3"))
                        t_sl = safe_float(up.get("new_stop_loss"))
                        
                        if t_tp1 > 0: cur2.execute("UPDATE positions SET tp1_price=%s WHERE id=%s", (t_tp1, pid))
                        if t_tp2 > 0: cur2.execute("UPDATE positions SET tp2_price=%s WHERE id=%s", (t_tp2, pid))
                        if t_tp3 > 0: cur2.execute("UPDATE positions SET tp3_price=%s WHERE id=%s", (t_tp3, pid))
                        if t_sl > 0 and not is_long:
                            cur2.execute("UPDATE positions SET stop_loss_price=%s WHERE id=%s", (t_sl, pid))
                    c2.commit()
                except Exception:
                    try: c2.rollback()
                    except: pass
                finally: release_conn(c2)
        with _cache_lock:
            if "main" in _cache: del _cache["main"]
    except Exception as e:
        update_log("deepseek", "error", f"巡检出错: {str(e)}")

def check_strats(d):
    global _last_ai_patrol, _last_breakout_price, _last_breakout_check
    if d.get("error") or not _strategy_lock.acquire(blocking=False): return
    try:
        tier = get_int_setting("bs_tier", 0)
        if tier > 0 and d["rsi"] > 50:
            set_setting("bs_tier", "0"); push_feishu("☀️ 危机解除", "市场企稳，RSI>50。")
        if tier < 1 and d["drawdown"] > 10 and d["rsi"] < 28:
            push_feishu("🩸 黑天鹅【一档】", f"回撤:{d['drawdown']}%\n动用20%备用金买入"); set_setting("bs_tier", "1")
        elif tier == 1 and d["drawdown"] > 18 and d["fng"] < 25:
            push_feishu("🔄 黑天鹅【二档】", f"回撤:{d['drawdown']}%\n动用30%备用金买入"); set_setting("bs_tier", "2")
        elif tier == 2 and d["drawdown"] > 25 and d["fng"] < 15:
            push_feishu("💎 黑天鹅【终极】", f"回撤:{d['drawdown']}%\n打入最后50%子弹！"); set_setting("bs_tier", "3")

        c = get_conn()
        if c:
            try:
                cur_db = c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
                cur_db.execute("SELECT * FROM positions WHERE status='open'")
                for p in cur_db.fetchall():
                    sl = p.get("stop_loss_price")
                    if not p.get("is_long_term", False) and sl is not None and d["current"] <= sl and not p["sl_hit"]:
                        push_feishu(f"⚠️ [仓位#{p['id']}] 跌破防守线", f"当前价 {d['current']} 已跌破 {sl}！请立刻打开App！")
                        cur_db.execute("UPDATE positions SET sl_hit=true WHERE id=%s", (p["id"],))
                        c.commit()
            except Exception:
                try: c.rollback()
                except: pass
            finally: release_conn(c)

        pm = get_int_setting("ai_patrol_minutes", 60)
        if pm > 0 and time.time() - _last_ai_patrol > pm * 60:
            _last_ai_patrol = time.time()
            threading.Thread(target=ai_patrol_worker, args=(d,), daemon=True).start()

        if time.time() - _last_breakout_check > 300 and _active_signal["data"] is None:
            rh = d.get("recent_high", 0)
            if rh > 0 and d["current"] > rh * 1.003 and rh > _last_breakout_price:
                _last_breakout_price = rh; _last_breakout_check = time.time()
                push_feishu("🚀 突破异动！", f"现价 {d['current']} 强势突破近期高点 {rh}！")
    finally: _strategy_lock.release()

# ============ API 端点 ============
@app.route("/api/cron_check")
def cron():
    try:
        d = get_market()
        if not d.get("error"): check_strats(d)
        return jsonify({"status": "ok"})
    except Exception: return jsonify({"status": "ok"})

@app.route("/api/current_data")
def cur_data():
    global _last_refresh
    f = request.args.get('force', 'false').lower() == 'true'
    if f and time.time() - _last_refresh > 10: _last_refresh = time.time()
    elif f: f = False
    if f:
        with _cache_lock:
            if "main" in _cache: del _cache["main"]
    d = get_market()
    if f and not d.get("error"): check_strats(d)
    return jsonify({"market": d, "tier": get_int_setting("bs_tier", 0)})

@app.route("/api/dismiss_signal", methods=["POST"])
def dismiss_signal_api():
    with _cache_lock:
        _active_signal["data"] = None
    return jsonify({"status": "ok"})

@app.route("/api/mark_long_term", methods=["POST"])
def mark_long_term():
    d = request.get_json(silent=True) or {}; pid = safe_int(d.get("id"))
    if not pid: return jsonify({"status": "error"})
    c = get_conn()
    if not c: return jsonify({"status": "error", "msg": "数据库暂时不可用"})
    try:
        cur = c.cursor()
        cur.execute("UPDATE positions SET is_long_term=true WHERE id=%s", (pid,))
        c.commit()
        push_feishu(f"🧘 [仓位#{pid}] 转长线", "已禁止AI提示短线止损。")
    except Exception:
        try: c.rollback()
        except: pass
    finally: release_conn(c)
    return jsonify({"status": "ok"})

@app.route("/api/evaluate_position", methods=["POST"])
def evaluate_position():
    d = request.get_json(silent=True) or {}; pid = safe_int(d.get("id"))
    c = get_conn(); pos = None
    if c:
        try:
            cur = c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
            cur.execute("SELECT * FROM positions WHERE id=%s", (pid,))
            pos = cur.fetchone()
        except Exception: pass
        finally: release_conn(c)
    if not pos: return jsonify({"status": "error", "msg": "仓位不存在或数据库维护中"})
    
    m = get_market()
    if m.get("error"): return jsonify({"status": "error", "msg": "当前行情获取失败，无法诊断"})
    
    cp = m.get("current") or 0
    entry = safe_float(pos.get("entry_price"))
    if entry <= 0: return jsonify({"status": "error", "msg": "仓位数据异常"})
    pnl_pct = (cp - entry) / entry * 100
    is_long = pos.get("is_long_term", False)
    
    prompt = f"持有【仓位#{pid}】，成本:{entry}, 现价:{cp}, 盈亏:{pnl_pct:.2f}%。当前全景：RSI:{m.get('rsi')}, 估值分:{m.get('val_score')}, 宏观:{m.get('macro_text')}, 盘口:{m.get('ob_text')}, 巨鲸:{m.get('whale_text')}, 稳定币溢价:{m.get('premium_text')}, 趋势:{m.get('mtf')}。"
    if is_long:
        prompt += "该仓位为【长线防守模式】，绝对禁止给出止损建议。输出JSON：{'action':'hold/wait_rebound', 'win_rate':90, 'days':30, 'reason':'按摩理由', 'price_tip':'加仓建议'}"
    else:
        prompt += "请给出处置建议。输出JSON：{'action':'hold/stop_loss/wait_rebound', 'win_rate':胜率, 'days':天数, 'reason':'大白话', 'price_tip':'执行价'}"
        
    rep = ask_ai(prompt)
    if not rep: return jsonify({"status": "error", "msg": "AI 服务超时或不可用，请点击下方按钮重试。"})
    try:
        res = json.loads(rep.replace("```json", "").replace("```", "").strip())
        if "win_rate" not in res: res["win_rate"] = "--"
        if "days" not in res: res["days"] = "--"
        if "reason" not in res: res["reason"] = "无"
        return jsonify({"status": "ok", "data": res, "pnl_pct": round(pnl_pct, 2), "is_long_term": is_long})
    except Exception: return jsonify({"status": "error", "msg": "AI 返回格式异常，请重试。"})

@app.route("/api/second_guess", methods=["POST"])
def second_guess():
    d = request.get_json(silent=True) or {}
    m = get_market()
    if m.get("error"): return jsonify({"action": "stop", "text": "行情获取失败，建议放弃本次操作。"})
    
    prompt = f"原限价区间:{d.get('low')}-{d.get('high')}，现价:{m.get('current')}。当前宏观:{m.get('macro_text')}, 盘口:{m.get('ob_text')}, 巨鲸:{m.get('whale_text')}。研判：1.追单(go) 2.等回踩(wait) 3.放弃(stop)。严格JSON: {{'action':'go/wait/stop', 'wait_price':数字, 'text':'理由'}}"
    rep = ask_ai(prompt)
    if rep:
        try: return jsonify(json.loads(rep.replace("```json", "").replace("```", "").strip()))
        except Exception: pass
    return jsonify({"action": "stop", "text": "AI 研判失败，建议放弃本次操作。"})

@app.route("/api/record_position", methods=["POST"])
def rec_pos():
    global _active_signal
    with _cache_lock:
        _active_signal["data"] = None
        
    d = request.get_json(silent=True) or {}
    try: price = safe_float(d.get("price", 0)); qty = safe_float(d.get("qty", 0))
    except: return jsonify({"status": "error", "msg": "参数无效"})
    if price <= 0 or qty <= 0: return jsonify({"status": "error", "msg": "数量必须大于0"})
    
    current_market_price = get_realtime_price()
    if current_market_price > 0:
        deviation = abs(price - current_market_price) / current_market_price
        if deviation > 0.05:
            return jsonify({"status": "error", "msg": f"风控拦截：输入价格({price})偏离当前市价({current_market_price})超过5%，请仔细核对！"})

    c = get_conn()
    if not c: return jsonify({"status": "error", "msg": "数据库维护中，暂无法记录仓位，请稍后再试。"})
    
    m = get_market()
    if m.get("error"):
        return jsonify({"status": "error", "msg": "当前行情获取失败，暂无法建仓"})
        
    ai_prompt = f"用户刚买入 BTC，买入价: {price}。当前全景：价格{m.get('current')}, RSI {m.get('rsi')}, 宏观{m.get('macro_text')}, 盘口{m.get('ob_text')}, 巨鲸{m.get('whale_text')}, 趋势{m.get('mtf')}。请制定三档止盈及防守止损线。严格输出JSON：{{\"tp1\": {{\"price\": 数字, \"win_rate\": 数字, \"days\": 数字}}, \"tp2\": {{\"price\": 数字, \"win_rate\": 数字, \"days\": 数字}}, \"tp3\": {{\"price\": 数字, \"win_rate\": 数字, \"days\": 数字}}, \"stop_loss\": 数字}}"
    rep = ask_ai(ai_prompt)
    
    default_targets = {
        "tp1": {"price": round(price*1.008,2), "win_rate": 85, "days": 1},
        "tp2": {"price": round(price*1.03,2), "win_rate": 65, "days": 3},
        "tp3": {"price": round(price*1.06,2), "win_rate": 45, "days": 7},
        "stop_loss": round(price*0.97, 2)
    }
    targets = default_targets
    
    if rep:
        try:
            parsed = json.loads(rep.replace("```json", "").replace("```", "").strip())
            if all(k in parsed and isinstance(parsed[k], dict) and "price" in parsed[k] for k in ["tp1","tp2","tp3"]):
                t_tp1 = safe_float(parsed["tp1"]["price"])
                t_tp2 = safe_float(parsed["tp2"]["price"])
                t_tp3 = safe_float(parsed["tp3"]["price"])
                t_sl = safe_float(parsed.get("stop_loss", default_targets["stop_loss"]))
                
                if t_sl >= price or t_tp1 <= price or t_tp2 <= price or t_tp3 <= price:
                    print("AI 给出反向止盈止损，已自动拦截并重置默认值")
                else:
                    targets = {
                        "tp1": {"price": t_tp1, "win_rate": safe_int(parsed["tp1"].get("win_rate"), 85), "days": safe_int(parsed["tp1"].get("days"), 1)},
                        "tp2": {"price": t_tp2, "win_rate": safe_int(parsed["tp2"].get("win_rate"), 65), "days": safe_int(parsed["tp2"].get("days"), 3)},
                        "tp3": {"price": t_tp3, "win_rate": safe_int(parsed["tp3"].get("win_rate"), 45), "days": safe_int(parsed["tp3"].get("days"), 7)},
                        "stop_loss": t_sl
                    }
        except Exception: pass
    
    new_id = "?"
    try:
        cur = c.cursor()
        cur.execute("INSERT INTO positions (entry_price, quantity, remaining_qty, entry_usdt, opened_at, tp1_price, tp2_price, tp3_price, stop_loss_price, tp_metadata) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s) RETURNING id",
            (price, qty, qty, price*qty, datetime.now(timezone.utc).isoformat(), targets["tp1"]['price'], targets["tp2"]['price'], targets["tp3"]['price'], targets["stop_loss"], json.dumps(targets)))
        new_id = cur.fetchone()[0]; c.commit()
    except Exception as e:
        try: c.rollback()
        except: pass
        return jsonify({"status": "error", "msg": f"数据库异常: {str(e)}"})
    finally: release_conn(c)
    
    push_feishu(f"🎯 [仓位#{new_id}] 建仓", f"买:{price}\n金额:{round(price*qty,2)}U\n止损:{targets['stop_loss']}\n1档:{targets['tp1']['price']}(胜率{targets['tp1']['win_rate']}%)\n2档:{targets['tp2']['price']}(胜率{targets['tp2']['win_rate']}%)\n3档:{targets['tp3']['price']}(胜率{targets['tp3']['win_rate']}%)")
    return jsonify({"status": "ok", "id": new_id})

@app.route("/api/positions")
def get_pos():
    global _pos_cache
    d = get_market(); cp = d.get("current") or 0
    c = get_conn()
    
    if not c:
        return jsonify({"positions": _pos_cache, "db_alive": False})
    
    pos = []
    try:
        cur = c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("SELECT * FROM positions WHERE status='open' ORDER BY id ASC")
        for r in cur.fetchall():
            entry = safe_float(r.get("entry_price"))
            qty = max(0.0, safe_float(r.get("remaining_qty")))
            pnl = ((cp - entry) / entry * 100) if cp and entry > 0 else 0
            try: tp_meta = json.loads(r.get("tp_metadata") or "{}")
            except Exception: tp_meta = {}
            
            for k in ["tp1", "tp2", "tp3"]:
                if k not in tp_meta: tp_meta[k] = {"price": "--", "win_rate": "--", "days": "--"}
                else:
                    if "price" not in tp_meta[k]: tp_meta[k]["price"] = "--"
                    if "win_rate" not in tp_meta[k]: tp_meta[k]["win_rate"] = "--"
                    if "days" not in tp_meta[k]: tp_meta[k]["days"] = "--"

            pos.append({
                "id": r["id"], 
                "entry_price": entry, 
                "remaining_qty": qty, 
                "entry_usdt": safe_float(r.get("entry_usdt")),
                "pnl_pct": round(pnl, 2), 
                "tp_metadata": tp_meta, 
                "tp1_hit": r.get("tp1_hit", False),
                "tp2_hit": r.get("tp2_hit", False),
                "tp3_hit": r.get("tp3_hit", False),
                "is_long_term": r.get("is_long_term", False)
            })
        _pos_cache = pos 
    except Exception: 
        return jsonify({"positions": _pos_cache, "db_alive": False})
    finally: release_conn(c)
    
    return jsonify({"positions": pos, "db_alive": _db_alive})

@app.route("/api/sell_position", methods=["POST"])
def sell_pos():
    d = request.get_json(silent=True) or {}; pid = safe_int(d.get("id"))
    try: sp = safe_float(d.get("price")); su = safe_float(d.get("usdt"))
    except: return jsonify({"status": "error", "msg": "参数无效"})
    if sp <= 0 or su <= 0: return jsonify({"status": "error", "msg": "金额必须大于0"})
    sq = round(su / sp, 6)
    c = get_conn()
    if not c: return jsonify({"status": "error", "msg": "数据库维护中"})
    try:
        cur = c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute("SELECT * FROM positions WHERE id=%s", (pid,))
        p = cur.fetchone()
        if p:
            remain = max(0.0, safe_float(p.get("remaining_qty")))
            if sq > remain: sq = remain; su = sq * sp
            rem = max(0, round(remain - sq, 6))
            if rem < 0.000001: rem = 0
            cur.execute("UPDATE positions SET remaining_qty=%s, status=%s WHERE id=%s", (rem, "closed" if rem==0 else "open", pid))
            c.commit()
            push_feishu(f"✅ [仓位#{pid}] 卖出确认", f"卖:{round(su,2)}U ({sq}BTC)\n剩:{rem}BTC")
    except Exception:
        try: c.rollback()
        except: pass
    finally: release_conn(c)
    return jsonify({"status": "ok"})

@app.route("/api/close_position", methods=["POST"])
def close_position():
    d = request.get_json(silent=True) or {}; pid = safe_int(d.get("id"))
    if not pid: return jsonify({"status": "error", "msg": "缺少ID"})
    c = get_conn()
    if not c: return jsonify({"status": "error", "msg": "数据库维护中"})
    try:
        cur = c.cursor()
        cur.execute("UPDATE positions SET status='closed', remaining_qty=0 WHERE id=%s", (pid,))
        c.commit()
        push_feishu(f"🚫 [仓位#{pid}] 强制平仓", "已手动强制平仓此仓位。")
    except Exception:
        try: c.rollback()
        except: pass
    finally: release_conn(c)
    return jsonify({"status": "ok"})

@app.route("/api/get_settings")
def get_sets():
    return jsonify({k: get_setting(k) for k in ["total_capital","target_capital","account_btc","account_usdt","reserve_ratio","short_term_amount","min_win_rate","feishu_webhook","deepseek_key","siliconflow_key","ai_patrol_minutes"]})

@app.route("/api/save_settings", methods=["POST"])
def save_sets():
    d = request.get_json(silent=True) or {}
    for k, v in d.items(): set_setting(k, v)
    return jsonify({"status": "ok"})

@app.route("/api/update_balance", methods=["POST"])
def upd_bal():
    d = request.get_json(silent=True) or {}
    if "btc" in d: set_setting("account_btc", d["btc"])
    if "usdt" in d: set_setting("account_usdt", d["usdt"])
    return jsonify({"status": "ok"})

@app.route("/api/chat", methods=["POST"])
def chat():
    d = get_market(); msg = (request.get_json(silent=True) or {}).get('message', '')
    if d.get("error"): return jsonify({"reply": "当前行情获取失败，无法分析"})
    rep = ask_ai(f"当前行情:{d.get('current')}, 宏观:{d.get('macro_text')}。用户问:{msg}。结合长线看多信仰回答。")
    return jsonify({"reply": rep or "AI休息中"})

@app.route('/manifest.json')
def manifest():
    return make_response(jsonify({"name": "BTC AI", "short_name": "BTC", "start_url": "/", "display": "standalone", "background_color": "#181A20", "theme_color": "#181A20", "icons": [{"src": "data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAxMDAgMTAwIj48cmVjdCB3aWR0aD0iMTAwIiBoZWlnaHQ9IjEwMCIgcng9IjIwIiBmaWxsPSIjMTgxQTIwIi8+PGNpcmNsZSBjeD0iNTAiIGN5PSI1MCIgcj0iMzAiIGZpbGw9IiNGQ0Q1MzUiLz48L3N2Zz4=", "sizes": "192x192", "type": "image/svg+xml"}]}))

# ============ 前端界面 ============
HOME = """
<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0,maximum-scale=1.0,user-scalable=no"><title>BTC AI</title><link rel="manifest" href="/manifest.json"><meta name="apple-mobile-web-app-capable" content="yes"><style>
:root{--bg:#181A20;--card:#2B3139;--text:#EAECEF;--sub:#848E9C;--yellow:#FCD535;--green:#0ECB81;--red:#F6465D;--blue:#58a6ff;--purple:#bc8cff}*{box-sizing:border-box;margin:0;padding:0;font-family:-apple-system,sans-serif}body{background:var(--bg);color:var(--text);padding:15px;padding-bottom:70px;padding-top:env(safe-area-inset-top,20px)}.card{background:var(--card);border-radius:12px;padding:15px;margin-bottom:15px}.price{font-size:40px;font-weight:bold;margin:10px 0}.badge{display:inline-block;padding:4px 10px;border-radius:6px;font-size:12px;background:#363C45;color:var(--sub)}.tag-green{color:var(--green)}.tag-red{color:var(--red)}.tag-yellow{color:var(--yellow)}.tag-blue{color:var(--blue)}.tag-purple{color:var(--purple)}.row{display:flex;justify-content:space-between;margin:10px 0;font-size:14px}.btn{display:block;width:100%;padding:12px;border-radius:8px;border:none;font-size:16px;font-weight:bold;margin-top:10px;cursor:pointer}.btn-yellow{background:var(--yellow);color:#000}.progress-bg{background:#363C45;border-radius:10px;height:12px;margin:10px 0;overflow:hidden}.progress-bar{background:var(--red);height:100%;width:0%;transition:width .3s}.header-bar{display:flex;justify-content:space-between;align-items:center;margin-bottom:15px}.btn-refresh{background:transparent;border:1px solid var(--sub);color:var(--text);padding:6px 12px;border-radius:8px;font-size:13px;cursor:pointer}.input-group{margin-bottom:15px}.input-group label{display:block;font-size:13px;color:var(--sub);margin-bottom:5px}.input-group input{width:100%;padding:12px;border-radius:8px;border:1px solid #363C45;background:#1E2329;color:#fff;font-size:15px}.bottom-nav{position:fixed;bottom:0;left:0;right:0;background:#1E2329;display:flex;justify-content:space-around;padding:10px 0;padding-bottom:env(safe-area-inset-bottom,10px);border-top:1px solid #363C45;z-index:90}.nav-item{color:var(--sub);font-size:12px;text-align:center;cursor:pointer}.nav-item.active{color:var(--yellow);font-weight:bold}.nav-icon{font-size:20px;display:block;margin-bottom:3px}
.detail-box{display:none; margin-top:15px; padding:15px; background:#1E2329; border-radius:8px; border:1px solid #363C45; font-family:monospace;}
.signal-box{display:none; border:2px dashed var(--green); background:rgba(14,203,129,0.1); border-radius:12px; padding:15px; margin-bottom:15px;}
.modal-overlay{display:none;position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,0.7);z-index:200;align-items:center;justify-content:center;}
.modal-box{background:var(--card);width:85%;max-width:400px;border-radius:12px;padding:20px;border:1px solid var(--yellow);}
#db-warning{display:none; background:var(--red); color:#fff; text-align:center; padding:10px; border-radius:8px; margin-bottom:15px; font-weight:bold; box-shadow:0 4px 12px rgba(246,70,93,0.3);}
</style></head><body>

<div id="page-home">
<div class="header-bar">
    <h2 style="font-size:18px">BTC 量化助手</h2>
    <div style="display:flex;gap:10px;align-items:center;">
        <span id="trend-badge" class="badge" style="background:#363C45;">加载中</span>
        <button id="refresh-btn" class="btn-refresh" onclick="manualRefresh()">🔄 刷新</button>
    </div>
</div>

<div id="db-warning">⚠️ Supabase 维护中，行情正常，仓位记录暂时冻结。恢复自动同步。</div>

<div class="card" style="background:linear-gradient(135deg,#2B3139,#1E2329);border:1px solid #363C45">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
        <span style="font-size:13px;color:var(--sub)">💼 我的账户总览</span>
        <button onclick="editBalance()" style="background:transparent;border:1px solid var(--yellow);color:var(--yellow);padding:2px 8px;border-radius:4px;font-size:12px;cursor:pointer">修改</button>
    </div>
    <div style="font-size:28px;font-weight:bold;color:var(--text);margin-bottom:5px">$ <span id="total-asset-value">--</span> <span style="font-size:14px;color:var(--sub);font-weight:normal">USDT</span></div>
    <div style="display:flex;gap:20px;font-size:13px;color:var(--sub)"><span>BTC: <strong id="acc-btc" style="color:var(--text)">--</strong></span><span>USDT: <strong id="acc-usdt" style="color:var(--text)">--</strong></span></div>
</div>

<div class="card" style="text-align:center; background:linear-gradient(180deg, #2B3139 0%, #1E2329 100%);">
    <div style="font-size:14px;color:var(--sub)">BTC/USDT 现价</div>
    <div class="price" id="btc-price">--</div>
    
    <div style="margin: 20px 0; padding: 15px; background:rgba(252,213,53,0.1); border-radius:8px;">
        <div style="font-size:13px; color:var(--yellow); margin-bottom:8px;">🧠 AI 全维前瞻结论</div>
        <div id="ai-forecast" style="font-size:18px; font-weight:bold; line-height:1.4; color:#fff;">加载中...</div>
    </div>
    
    <div style="display:flex; justify-content:space-between; font-size:13px; color:var(--sub);">
        <span>综合估值评分: <strong id="val-score" style="color:var(--green)">--</strong></span>
        <span>恐慌贪婪: <strong id="fng-val" style="color:var(--blue)">--</strong></span>
    </div>
    
    <button onclick="toggleDetail()" style="margin-top:15px; background:transparent; border:1px solid var(--sub); color:var(--sub); padding:8px 15px; border-radius:8px; font-size:13px; width:100%; cursor:pointer;">👉 点击查看底层全维度数据</button>
    
    <div id="detail-panel" class="detail-box"></div>
</div>

<div id="signal-card" class="signal-box">
    <div style="display:flex; justify-content:space-between; margin-bottom:10px;">
        <strong style="color:var(--green); font-size:15px;">🔥 AI 高胜率交易计划</strong>
    </div>
    
    <div style="background:rgba(0,0,0,0.2); border-radius:8px; padding:10px; margin-bottom:10px;">
        <div style="font-size:13px; color:var(--yellow); margin-bottom:5px;">🟢 左侧限价挂单 (接针)</div>
        <div style="font-size:14px; margin-bottom:8px;">区间: <strong id="sig-range"></strong> (胜率 <span id="sig-winrate"></span>%)</div>
        <button class="btn" style="background:var(--yellow); color:#000; padding:8px; margin-top:0; font-size:14px;" onclick="recordPosition('limit')">记录我已挂限价单</button>
    </div>

    <div style="background:rgba(0,0,0,0.2); border-radius:8px; padding:10px; margin-bottom:10px;">
        <div style="font-size:13px; color:var(--blue); margin-bottom:5px;">🔵 右侧市价追单 (突破)</div>
        <div style="font-size:14px; margin-bottom:8px;">突破 <strong id="sig-mkt-trigger"></strong> 时市价 (胜率 <span id="sig-mkt-winrate"></span>%)</div>
        <button class="btn" style="background:var(--blue); color:#fff; padding:8px; margin-top:0; font-size:14px;" onclick="recordPosition('market')">记录我已市价追多</button>
    </div>

    <div style="font-size:13px; margin-bottom:5px;">⏱ 预计达成: <strong id="sig-days" style="color:var(--purple)"></strong> 天 | ⏳ 剩余: <span id="sig-ttl" style="color:var(--red); font-weight:bold;"></span></div>
    
    <div style="display:flex; gap:10px; margin-top:15px;">
        <button class="btn" style="flex:1; background:var(--purple); color:#fff; font-size:13px; padding:8px;" onclick="markSignalLongTerm()">🧘 转长线死拿</button>
        <button class="btn" style="flex:1; background:#363C45; color:var(--sub); font-size:13px; padding:8px;" onclick="dismissSignal()">❌ 强制放弃计划</button>
    </div>
</div>

<div class="card">
    <h3 style="font-size:15px; margin-bottom:15px;">💼 我的持仓记录</h3>
    <button class="btn" style="background:#363C45; color:#fff; font-size:13px; padding:10px; margin-bottom:15px;" onclick="recordPosition('manual')">✍️ 记录新买入仓位</button>
    <div id="positions-area">
        <div style="color:var(--sub);text-align:center;padding:20px">当前空仓，耐心等待猎物。</div>
    </div>
</div>

<div class="card">
    <h3 style="font-size:15px;margin-bottom:15px">🦅 黑天鹅抄底雷达</h3>
    <div class="row"><span>当前防御档位</span><span id="bs-status" class="tag-yellow">安全 (0/3)</span></div>
    <div class="progress-bg"><div class="progress-bar" id="bs-progress" style="width: 0%;"></div></div>
</div>

<div class="card">
    <h3 style="font-size:15px;margin-bottom:10px;">🔍 接口运行状态</h3>
    <button onclick="toggleLogs()" style="background:transparent; border:1px solid var(--sub); color:var(--sub); padding:6px; border-radius:6px; font-size:12px; width:100%;">展开/收起日志</button>
    <div id="log-panel" class="detail-box" style="font-size:12px;"></div>
</div>
</div>

<div id="page-settings" style="display:none">
    <h2 style="font-size:20px;margin-bottom:20px">⚙️ 设置中心</h2>
    <div class="card">
        <div class="input-group"><label>DeepSeek API Key</label><input type="password" id="set-deepseek"></div>
        <div class="input-group"><label>硅基流动 Key(备选)</label><input type="password" id="set-siliconflow"></div>
        <div class="input-group"><label>飞书 Webhook</label><input type="text" id="set-feishu"></div>
        <div class="input-group"><label>AI自动巡检间隔 (分钟)</label><input type="number" id="set-patrol-mins" placeholder="60"></div>
        <div class="input-group"><label>最低胜率要求 (%)</label><input type="number" id="set-min-win" placeholder="60"></div>
    </div>
    <button class="btn btn-yellow" onclick="saveSettings()" style="margin-bottom:30px">💾 保存设置</button>
</div>

<div class="bottom-nav">
    <div class="nav-item active" id="nav-home" onclick="switchPage('home')"><span class="nav-icon">📈</span>首页</div>
    <div class="nav-item" id="nav-settings" onclick="switchPage('settings')"><span class="nav-icon">⚙️</span>设置</div>
</div>

<div style="position:fixed;bottom:80px;right:20px;z-index:99">
    <button onclick="toggleAIPanel()" style="width:56px;height:56px;border-radius:50%;background:var(--yellow);color:#000;border:none;font-size:24px;box-shadow:0 4px 12px rgba(252,213,53,.4);cursor:pointer">🧠</button>
</div>

<div id="ai-panel" style="display:none;position:fixed;bottom:0;left:0;right:0;height:70vh;background:var(--card);border-radius:20px 20px 0 0;z-index:100;padding:20px;box-shadow:0 -10px 30px rgba(0,0,0,.5);overflow-y:auto">
    <div style="display:flex;justify-content:space-between;margin-bottom:15px">
        <h3 style="color:var(--yellow)">🧠 AI 智囊团</h3>
        <button onclick="toggleAIPanel()" style="background:none;border:none;color:var(--text);font-size:16px">✖ 关闭</button>
    </div>
    <div id="chat-box" style="height:300px;overflow-y:auto;background:#1E2329;border-radius:8px;padding:10px;margin-bottom:10px;font-size:13px;line-height:1.6">
        <div style="color:var(--sub)">你好，我已经把所有盘口、宏观、链上数据吃透了，有问题随时问我。</div>
    </div>
    <div style="display:flex;gap:10px">
        <input type="text" id="chat-input" placeholder="问点什么..." style="flex:1;padding:10px;border-radius:8px;border:1px solid #363C45;background:#1E2329;color:#fff">
        <button onclick="sendChat()" style="padding:10px 15px;background:var(--yellow);border:none;border-radius:8px;font-weight:bold">发送</button>
    </div>
</div>

<div id="rescue-modal" class="modal-overlay">
    <div class="modal-box" style="border-color: #58a6ff;">
        <h3 style="color:#58a6ff;margin-bottom:15px;font-size:18px;" id="rescue-title">🧠 AI 仓位急救</h3>
        <div id="rescue-content" style="font-size:14px;line-height:1.6;margin-bottom:20px;"></div>
        <button onclick="document.getElementById('rescue-modal').style.display='none'" class="btn btn-yellow">我知道了</button>
    </div>
</div>

<div id="second-guess-modal" class="modal-overlay">
    <div class="modal-box" style="border-color: var(--red);">
        <h3 style="color:var(--red);margin-bottom:15px;font-size:18px;">⚠️ 行情已偏离原限价区间</h3>
        <div id="sg-content" style="font-size:14px;line-height:1.6;margin-bottom:20px;color:var(--text);"></div>
        <div style="display:flex; gap:10px;">
            <button id="sg-btn-market" onclick="executeMarketOrder()" style="flex:1;padding:10px;background:var(--red);border:none;border-radius:8px;font-weight:bold;color:#fff;cursor:pointer;">立刻市价追单</button>
            <button id="sg-btn-wait" onclick="executeLimitOrder()" style="flex:1;padding:10px;background:var(--yellow);border:none;border-radius:8px;font-weight:bold;color:#000;cursor:pointer;display:none;">按建议价挂单</button>
            <button onclick="closeSGModal()" style="flex:1;padding:10px;background:#363C45;border:none;border-radius:8px;color:#fff;cursor:pointer;">彻底放弃</button>
        </div>
    </div>
</div>

<script>
let globalCurrentPrice=0, globalBtcBal=0, globalUsdtBal=0;
let signalTimer = null, currentSignal = null, secondGuessPending = false, sgData = null;
let lastSignalData = null;
let isRecording = false;
let isFetching = false;
let isDismissing = false;

function fetchWithTimeout(url, options = {}, timeout = 5000) {
    const controller = new AbortController();
    const id = setTimeout(() => controller.abort(), timeout);
    return fetch(url, {
        ...options,
        signal: controller.signal
    }).finally(() => {
        clearTimeout(id);
    });
}

function switchPage(p){
    document.getElementById('page-home').style.display=p==='home'?'block':'none';
    document.getElementById('page-settings').style.display=p==='settings'?'block':'none';
    document.getElementById('nav-home').className='nav-item '+(p==='home'?'active':'');
    document.getElementById('nav-settings').className='nav-item '+(p==='settings'?'active':'');
    if(p==='settings') loadSettings();
}

function toggleDetail(){ let d = document.getElementById('detail-panel'); d.style.display = d.style.display === 'block' ? 'none' : 'block'; }
function toggleLogs(){ let d = document.getElementById('log-panel'); d.style.display = d.style.display === 'block' ? 'none' : 'block'; }
function toggleAIPanel(){ let p = document.getElementById('ai-panel'); p.style.display = p.style.display === 'none' ? 'block' : 'none'; }

function fetchBalance(){
    fetchWithTimeout('/api/get_settings').then(r=>r.json()).then(d=>{
        globalBtcBal = parseFloat(d.account_btc||0);
        globalUsdtBal = parseFloat(d.account_usdt||0);
        document.getElementById('acc-btc').innerText = globalBtcBal;
        document.getElementById('acc-usdt').innerText = globalUsdtBal;
        calcTotalAssets();
    });
}
function calcTotalAssets(){
    if(globalCurrentPrice>0){
        document.getElementById('total-asset-value').innerText = ((globalBtcBal*globalCurrentPrice)+globalUsdtBal).toFixed(2);
    } else {
        document.getElementById('total-asset-value').innerText = "--";
    }
}
function editBalance(){
    let b = prompt("账户里的 BTC 总数量:", globalBtcBal);
    if(b===null) return;
    let u = prompt("账户里的 USDT 总数量:", globalUsdtBal);
    if(u===null) return;
    fetchWithTimeout('/api/update_balance',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({btc:parseFloat(b)||0,usdt:parseFloat(u)||0})})
    .then(r=>r.json()).then(d=>{ if(d.status==='ok') fetchBalance(); });
}

function loadSettings(){
    fetchWithTimeout('/api/get_settings').then(r=>r.json()).then(d=>{
        document.getElementById('set-deepseek').value = d.deepseek_key||'';
        document.getElementById('set-siliconflow').value = d.siliconflow_key||'';
        document.getElementById('set-feishu').value = d.feishu_webhook||'';
        document.getElementById('set-patrol-mins').value = d.ai_patrol_minutes ?? '60';
        document.getElementById('set-min-win').value = d.min_win_rate ?? '60';
    });
}
function saveSettings(){
    let d = {
        deepseek_key: document.getElementById('set-deepseek').value,
        siliconflow_key: document.getElementById('set-siliconflow').value,
        feishu_webhook: document.getElementById('set-feishu').value,
        ai_patrol_minutes: document.getElementById('set-patrol-mins').value,
        min_win_rate: document.getElementById('set-min-win').value
    };
    fetchWithTimeout('/api/save_settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(d)})
    .then(r=>r.json()).then(res=>{ if(res.status==='ok'){ alert('✅ 已保存'); switchPage('home'); fetchData(); } });
}

function dismissSignal(){
    if(isDismissing) return;
    isDismissing = true;
    document.getElementById('signal-card').style.display = 'none';
    currentSignal = null;
    if(signalTimer){ clearInterval(signalTimer); signalTimer = null; }
    fetchWithTimeout('/api/dismiss_signal', {method:'POST'}).finally(()=>{ isDismissing = false; });
}

function markSignalLongTerm(){
    if(!currentSignal) return;
    alert("提示：请先在下方【我的持仓记录】中买入并记录后，点击该仓位的【🧘 转长线】按钮。");
}

function updateSignalCard(sig){
    if(!sig) { document.getElementById('signal-card').style.display = 'none'; return; }
    if(globalCurrentPrice <= 0) return;

    if(globalCurrentPrice < sig.entry_low || globalCurrentPrice > sig.entry_high){
        if(!secondGuessPending){
            secondGuessPending = true;
            triggerSecondGuess(sig, "价格脱离限价区间");
        }
        dismissSignal(); return;
    }
    
    document.getElementById('signal-card').style.display = 'block';
    document.getElementById('sig-range').innerText = `$${sig.entry_low} - $${sig.entry_high}`;
    document.getElementById('sig-winrate').innerText = sig.win_rate;
    document.getElementById('sig-mkt-trigger').innerText = sig.market_trigger ? `$${sig.market_trigger}` : '暂无';
    document.getElementById('sig-mkt-winrate').innerText = sig.market_win_rate || '--';
    document.getElementById('sig-days').innerText = sig.days || 3;
    
    let remain = Math.floor(sig.ttl - ((Date.now()/1000) - sig.time));
    if(remain < 0) remain = 0;
    document.getElementById('sig-ttl').innerText = `${Math.floor(remain/60)}分${remain%60}秒`;
}

function triggerSecondGuess(sig, reason) {
    lastSignalData = sig;
    fetchWithTimeout('/api/second_guess', { method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({type: 'buy', low: sig.entry_low, high: sig.entry_high, reason: reason}) }, 10000)
    .then(r => r.json()).then(res => {
        sgData = res;
        let content = `原建议区间：$${sig.entry_low} - $${sig.entry_high}<br><br><b>AI 研判：</b>${res.text}`;
        document.getElementById('sg-content').innerHTML = content;
        
        if (res.action === 'go') {
            document.getElementById('sg-btn-market').style.display = 'block';
            document.getElementById('sg-btn-wait').style.display = 'none';
        } else if (res.action === 'wait') {
            content += `<br><br><span style="color:var(--yellow); font-weight:bold;">👉 建议回踩至 $${res.wait_price} 附近再买入</span>`;
            document.getElementById('sg-content').innerHTML = content;
            document.getElementById('sg-btn-market').style.display = 'none';
            document.getElementById('sg-btn-wait').style.display = 'block';
        } else {
            document.getElementById('sg-btn-market').style.display = 'none';
            document.getElementById('sg-btn-wait').style.display = 'none';
        }
        
        document.getElementById('second-guess-modal').style.display = 'flex';
    }).catch(() => {
        document.getElementById('sg-content').innerHTML = `
            <div style="color:var(--red); margin-bottom:15px;">AI 服务超时或不可用。</div>
            <div style="color:var(--sub); font-size:13px;">请根据当前盈亏自行决定是否在币安市价追单，或稍后重试。</div>
            <button class="btn btn-yellow" style="margin-top:15px; font-size:14px; padding:8px;" onclick="triggerSecondGuess(lastSignalData, '人工重试')">🔄 重新呼叫二次研判</button>
        `;
        document.getElementById('sg-btn-market').style.display = 'block';
        document.getElementById('sg-btn-wait').style.display = 'none';
        document.getElementById('second-guess-modal').style.display = 'flex';
    });
}

function executeMarketOrder() { closeSGModal(); alert(`✅ 已确认。请立刻去币安执行【市价买入】！`); recordPosition('market'); }
function executeLimitOrder() {
    closeSGModal();
    if(sgData && sgData.wait_price) alert(`✅ 建议去币安挂限价买单，价格: $${sgData.wait_price}`);
    recordPosition('limit');
}
function closeSGModal() { document.getElementById('second-guess-modal').style.display = 'none'; sgData = null; }

function fetchPositions(){
    fetchWithTimeout('/api/positions', {}, 8000).then(r=>r.json()).then(res=>{
        let warn = document.getElementById('db-warning');
        if(res.db_alive === false) warn.style.display = 'block';
        else warn.style.display = 'none';
        
        let a = document.getElementById('positions-area');
        if(res.positions && res.positions.length > 0){
            let h = '';
            res.positions.forEach(p=>{
                let c = p.pnl_pct >= 0 ? 'tag-green' : 'tag-red';
                let current_val = p.remaining_qty * globalCurrentPrice;
                let entry_val = p.entry_usdt || (p.entry_price * p.remaining_qty);
                
                let tp1 = p.tp_metadata?.tp1 || { price: '--', win_rate: '--', days: '--' };
                let tp2 = p.tp_metadata?.tp2 || { price: '--', win_rate: '--', days: '--' };
                let tp3 = p.tp_metadata?.tp3 || { price: '--', win_rate: '--', days: '--' };
                
                let hit1 = p.tp1_hit ? '已达成' : '待触发';
                let hit2 = p.tp2_hit ? '已达成' : '待触发';
                let hit3 = p.tp3_hit ? '已达成' : '待触发';
                let c1 = p.tp1_hit ? 'color:var(--sub); text-decoration:line-through;' : '';
                let c2 = p.tp2_hit ? 'color:var(--sub); text-decoration:line-through;' : '';
                let c3 = p.tp3_hit ? 'color:var(--sub); text-decoration:line-through;' : '';

                h += `<div style="background:#1E2329; padding:12px; border-radius:8px; margin-bottom:10px; border-left:3px solid ${p.is_long_term?'var(--purple)':(p.pnl_pct>=0?'var(--green)':'var(--red)')}">
                    <div style="display:flex; justify-content:space-between; margin-bottom:8px;">
                        <strong style="color:var(--yellow);">仓位 #${p.id} ${p.is_long_term?'[长线]':''}</strong>
                        <span class="${c}">${p.pnl_pct>0?'+':''}${p.pnl_pct}%</span>
                    </div>
                    <div style="font-size:13px; color:var(--sub); margin-bottom:5px;">成本价: ${p.entry_price} | 剩余数量: ${p.remaining_qty} BTC</div>
                    <div style="font-size:13px; color:var(--sub); margin-bottom:10px;">💰 买入金额: ~${entry_val.toFixed(2)}U | 当前估值: ~${current_val.toFixed(2)}U</div>
                    
                    <div style="background:#2B3139; border-radius:6px; padding:10px; margin-bottom:10px; font-size:12px;">
                        <div style="color:var(--yellow); margin-bottom:6px; font-weight:bold;">🎯 阶段性止盈计划</div>
                        <div style="display:flex; justify-content:space-between; margin-bottom:6px; ${c1}">
                            <span>🥩 1档 (${hit1})</span>
                            <span>价格: $${tp1.price} | 胜率: <span style="color:var(--green)">${tp1.win_rate}%</span> | 预计: ${tp1.days}天</span>
                        </div>
                        <div style="display:flex; justify-content:space-between; margin-bottom:6px; ${c2}">
                            <span>🍖 2档 (${hit2})</span>
                            <span>价格: $${tp2.price} | 胜率: <span style="color:var(--green)">${tp2.win_rate}%</span> | 预计: ${tp2.days}天</span>
                        </div>
                        <div style="display:flex; justify-content:space-between; ${c3}">
                            <span>🍗 3档 (${hit3})</span>
                            <span>价格: $${tp3.price} | 胜率: <span style="color:var(--green)">${tp3.win_rate}%</span> | 预计: ${tp3.days}天</span>
                        </div>
                    </div>

                    <div style="display:flex; gap:10px; margin-bottom:10px;">
                        <button class="btn" style="flex:1; padding:8px; font-size:12px; background:#58a6ff; color:#fff;" onclick="rescue(${p.id})">🧠 AI诊断</button>
                        <button class="btn" style="flex:1; padding:8px; font-size:12px; background:var(--yellow); color:#000;" onclick="sell(${p.id})">卖出记录</button>
                        ${!p.is_long_term ? `<button class="btn" style="flex:1; padding:8px; font-size:12px; background:var(--purple); color:#fff;" onclick="markPositionLongTerm(${p.id})">🧘 转长线</button>` : ''}
                    </div>
                    <button class="btn" style="padding:8px; font-size:12px; background:var(--red); color:#fff; margin-top:0;" onclick="forceClosePosition(${p.id})">❌ 强制平仓并关闭</button>
                </div>`;
            });
            a.innerHTML = h;
        } else {
            a.innerHTML = '<div style="color:var(--sub);text-align:center;padding:20px">当前空仓，耐心等待猎物。</div>';
        }
    });
}

function recordPosition(type){
    if(isRecording) return;
    isRecording = true;

    let title = "记录买入";
    if(type === 'limit') title = "记录左侧限价挂单成交";
    if(type === 'market') title = "记录右侧市价追单成交";

    let p = prompt(title + " - 买入均价 (USDT):", globalCurrentPrice.toFixed(2));
    if(!p) { isRecording = false; return; }
    let q = prompt(title + " - 买入数量 (BTC):", "0.01");
    if(!q) { isRecording = false; return; }
    
    alert("正在呼叫 AI 制定三档止盈计划，请稍候...");
    
    fetchWithTimeout('/api/record_position',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({price:parseFloat(p),qty:parseFloat(q)})}, 25000)
    .then(r=>r.json()).then(d=>{
        if(d.status==='ok'){ alert('✅ 仓位已记录'); dismissSignal(); fetchPositions(); }
        else alert("❌ 记录失败：" + (d.msg || "未知错误"));
    }).catch(()=>{ alert("❌ 网络或 AI 超时，请重试"); })
    .finally(()=>{ isRecording = false; });
}

function sell(id){
    let u = prompt("卖出金额 (USDT):", "100");
    if(!u) return;
    let p = prompt("卖出均价:", globalCurrentPrice.toFixed(2));
    if(!p) return;
    fetchWithTimeout('/api/sell_position',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:id,price:parseFloat(p),usdt:parseFloat(u)})})
    .then(r=>r.json()).then(d=>{ if(d.status==='ok'){ alert('✅ 已卖出'); fetchPositions(); } else alert(d.msg||"失败"); });
}

function markPositionLongTerm(id) {
    if(!confirm("确认将此仓位转为长线防守模式？\nAI 将不再提示短线止损。")) return;
    fetchWithTimeout('/api/mark_long_term', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({id: id}) })
    .then(r => r.json()).then(d => { if(d.status === 'ok') { fetchPositions(); } else alert(d.msg||"失败"); });
}

function forceClosePosition(id) {
    if(!confirm("⚠️ 警告：确认直接强制平仓并关闭该仓位吗？\n此操作将把剩余数量清零，不可恢复。")) return;
    fetchWithTimeout('/api/close_position', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({id: id}) })
    .then(r => r.json()).then(d => { if(d.status === 'ok') { alert('✅ 仓位已关闭'); fetchPositions(); } else alert(d.msg||"失败"); });
}

function rescue(id){
    document.getElementById('rescue-modal').style.display = 'flex';
    document.getElementById('rescue-content').innerHTML = '<div style="text-align:center; padding:20px;"><span class="spinner" style="border-color:#58a6ff; width:20px; height:20px;"></span> AI 正在深度扫描盘面，为你寻找解套方案...</div>';
    fetchWithTimeout('/api/evaluate_position',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:id})}, 25000)
    .then(r=>r.json()).then(res=>{
        if(res.status==='ok'){
            let d = res.data;
            let color = d.action==='hold'?'var(--green)':(d.action==='stop_loss'?'var(--red)':'var(--yellow)');
            document.getElementById('rescue-content').innerHTML = `
                <div style="font-size:16px; font-weight:bold; color:${color}; margin-bottom:10px;">
                    AI 结论: ${d.action==='hold'?'坚定持有':(d.action==='stop_loss'?'立刻止损':'等反弹出')}
                </div>
                <div class="row"><span>预测胜率</span><span style="color:var(--yellow); font-weight:bold;">${d.win_rate}%</span></div>
                <div class="row"><span>预计天数</span><span style="color:var(--yellow); font-weight:bold;">${d.days} 天</span></div>
                <div style="margin:10px 0; color:var(--sub); background:rgba(255,255,255,0.05); padding:10px; border-radius:6px;">理由: ${d.reason}</div>
                <div style="color:var(--yellow); font-weight:bold;">${d.price_tip||''}</div>
            `;
        } else {
            document.getElementById('rescue-content').innerHTML = `
                <div style="color:var(--red); margin-bottom:15px; font-weight:bold;">${res.msg}</div>
                <div style="color:var(--sub); font-size:13px; margin-bottom:15px;">可能是网络波动或 AI 接口限流。你可以稍后在下方点击重试：</div>
                <button class="btn btn-yellow" style="margin-top:0; font-size:14px; padding:10px;" onclick="rescue(${id})">🔄 重新呼叫 AI 诊断此仓位</button>
            `;
        }
    }).catch(() => {
        document.getElementById('rescue-content').innerHTML = `
            <div style="color:var(--red); margin-bottom:15px; font-weight:bold;">网络请求失败，AI 无法响应。</div>
            <button class="btn btn-yellow" style="margin-top:0; font-size:14px; padding:10px;" onclick="rescue(${id})">🔄 重新呼叫 AI 诊断此仓位</button>
        `;
    });
}

function sendChat(){
    let i = document.getElementById('chat-input'), m = i.value.trim();
    if(!m) return;
    let b = document.getElementById('chat-box');
    b.innerHTML += `<div style="text-align:right;margin-bottom:5px;color:var(--yellow)">你: ${m}</div>`;
    i.value='';
    fetchWithTimeout('/api/chat',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({message:m})}, 25000)
    .then(r=>r.json()).then(d=>{
        b.innerHTML += `<div style="color:#0ECB81;margin-bottom:10px">AI: ${d.reply}</div>`;
        b.scrollTop = b.scrollHeight;
    });
}

function renderLogs(logs){
    if(!logs) return;
    let html = '';
    const names = {"okx_kline":"K线数据","macro":"宏观环境","news":"新闻快讯","derivatives":"衍生品","orderbook":"盘口深度","whale":"巨鲸动向","fng":"恐慌指数","deepseek":"AI大脑","db":"数据库","stablecoin":"稳定币"};
    for(let k in logs){
        let d = logs[k];
        let c = "status-error", t = "异常";
        if(d.status==='ok') { c="status-ok"; t="正常"; }
        else if(d.status==='backup') { c="status-backup"; t="备用"; }
        else if(d.status==='skip') { c="status-skip"; t="跳过"; }
        html += `<div class="log-item"><span>${names[k]||k}</span><span class="${c}">${t}</span></div>`;
    }
    document.getElementById('log-panel').innerHTML = html;
}

function updateUI(r){
    if(r.market && r.market.error) return;
    let m = r.market; globalCurrentPrice = m.current;
    
    let warn = document.getElementById('db-warning');
    if(m.db_alive === false) warn.style.display = 'block';
    else warn.style.display = 'none';
    
    document.getElementById('btc-price').innerText = "$" + m.current.toFixed(2);
    document.getElementById('ai-forecast').innerText = m.verdict;
    document.getElementById('val-score').innerText = m.val_score;
    document.getElementById('fng-val').innerText = m.fng;
    document.getElementById('detail-panel').innerHTML = m.detail;
    renderLogs(m.logs);
    
    let bd = document.getElementById('trend-badge');
    bd.innerText = m.trend;
    bd.className = 'badge ' + (m.trend==='多头'?'tag-green':(m.trend==='空头'?'tag-red':'tag-yellow'));
    
    let tier = r.tier || 0;
    document.getElementById('bs-status').innerText = tier===0?'安全 (0/3)':(tier===1?'一档 (1/3)':(tier===2?'二档 (2/3)':'终极 (3/3)'));
    document.getElementById('bs-progress').style.width = (tier*33.3) + '%';
    
    calcTotalAssets();
    
    if(m.active_signal){
        if(!currentSignal || currentSignal.time !== m.active_signal.time){
            currentSignal = m.active_signal;
            secondGuessPending = false;
            if(signalTimer) clearInterval(signalTimer);
            signalTimer = setInterval(()=>updateSignalCard(currentSignal), 1000);
        }
        updateSignalCard(m.active_signal);
    } else {
        if(currentSignal) dismissSignal();
    }
    
    fetchPositions();
}

function fetchData(){
    if(isFetching) return;
    isFetching = true;
    fetchWithTimeout('/api/current_data', {}, 15000).then(r=>r.json()).then(r=>{
        updateUI(r);
    }).catch(() => {}).finally(() => { isFetching = false; });
}

function manualRefresh(){
    let btn = document.getElementById('refresh-btn'); 
    btn.innerText = "刷新中...";
    fetchWithTimeout('/api/current_data?force=true', {}, 15000).then(r=>r.json()).then(r=>{
        updateUI(r);
        btn.innerText = "🔄 刷新";
    }).catch(() => { btn.innerText = "🔄 刷新"; });
}

fetchData();
fetchBalance();
setInterval(fetchData, 30000);
</script>
</body></html>
"""

@app.route("/")
def idx(): return render_template_string(HOME)

if __name__ == "__main__":
    try: init_db()
    except Exception: pass
    threading.Thread(target=db_health_worker, daemon=True).start()
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
