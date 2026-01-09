
"""
USGS Earthquake Monitor -> Discord (Market-Rule Aware)
------------------------------------------------------
Monitors earthquakes and matches them against multiple Polymarket prediction markets.

OLD MARKETS (2025):
  1) LA 50-mile: >= 6.5 within 50 miles of Los Angeles between 2025-06-09 00:00:00 ET
     and 2025-12-31 23:59:59 ET.
  2) Megaquake 1: >= 8.0 anywhere between 2025-10-30 00:00:00 ET and 2025-11-30 23:59:59 ET.
  3) Megaquake 2: >= 8.0 anywhere between 2025-09-30 00:00:00 ET and 2025-12-31 23:59:59 ET.
  4) 7.0+ Rule 1: >= 7.0 anywhere between 2025-10-30 19:00:00 ET and 2025-11-15 23:59:59 ET.
  5) 7.0+ Rule 2: >= 7.0 anywhere between 2025-10-30 19:00:00 ET and 2025-11-30 23:59:59 ET.

NEW MARKETS (2026):
  6) 10.0+ earthquake before 2027 (all of 2026)
  7) 9.0+ earthquake before 2027 (all of 2026)
  8) Megaquake by January 31, 2026
  9) Megaquake by March 31, 2026
  10) Megaquake by June 30, 2026
  11) Another 7.0+ earthquake by March 31, 2026
  12) How many 7.0+ earthquakes by June 30, 2026 (counting market)
  13) How many 6.5+ earthquakes by January 11, 2026 (counting market)
  14) How many 6.5+ earthquakes by January 18, 2026 (counting market)
  15) How many 7.0+ earthquakes in 2026 (counting market)

Also:
  - Alerts on all >= 6.4 quakes (global critical), even if not in a market window.
  - For any quake that triggers a market, keep a 24h "pending window" where magnitude
    revisions may occur; updates re-alert and the latest value at 24h is considered final.
  - Haversine distance; 50 miles = 80.4672 km.
  - USGS FDSN Event API polling; Discord webhook notifications.
  - Persists seen IDs and pending market windows in JSON files.

Setup:
  pip install requests web3 eth-account
  Edit eq_monitor.py and set:
    - DISCORD_WEBHOOK_URL (required)
    - POLYMARKET_PRIVATE_KEY (optional, for auto-trading)
    - POLYMARKET_TRADE_AMOUNT_USD (optional, default 10)
  python eq_monitor.py
"""

import json
import time
import math
import random
import logging
from datetime import datetime, timedelta, timezone
from typing import Dict, Any, List, Set, Tuple, Optional
from zoneinfo import ZoneInfo

import requests
from web3 import Web3
from eth_account import Account

# -------------------- Config -------------------- #
USGS_ENDPOINT = "https://earthquake.usgs.gov/fdsnws/event/1/query"
POLL_MIN_SEC = 5
POLL_MAX_SEC = 10
LOOKBACK_HOURS = 2
CRITICAL_MAG = 6.4
HEARTBEAT_TZ = "Asia/Jerusalem"  # Timezone for heartbeat
HEARTBEAT_HOUR = 16  # Hour (24h format) to send heartbeat
HEARTBEAT_FILE = "heartbeat_state.json"

# Reference & distances
LOS_ANGELES = (34.0522, -118.2437)
FIFTY_MILES_KM = 80.4672  # exact 50 miles

# Markets windows (ET). We'll construct aware datetimes in ET (UTC-4 during this period).
# For strict TZ handling, swap to zoneinfo("America/New_York").
ET = timezone(timedelta(hours=-4), name="ET")

# ========== OLD MARKETS (2025) ==========
LA_START_ET = datetime(2025, 6, 9, 0, 0, 0, tzinfo=ET)
LA_END_ET   = datetime(2025, 12, 31, 23, 59, 59, tzinfo=ET)

MEGA1_START_ET = datetime(2025, 10, 30, 0, 0, 0, tzinfo=ET)
MEGA1_END_ET   = datetime(2025, 11, 30, 23, 59, 59, tzinfo=ET)

MEGA2_START_ET = datetime(2025, 9, 30, 0, 0, 0, tzinfo=ET)
MEGA2_END_ET   = datetime(2025, 12, 31, 23, 59, 59, tzinfo=ET)

ANY7_1_START_ET = datetime(2025, 10, 30, 19, 0, 0, tzinfo=ET)
ANY7_1_END_ET   = datetime(2025, 11, 15, 23, 59, 59, tzinfo=ET)

ANY7_2_START_ET = datetime(2025, 10, 30, 19, 0, 0, tzinfo=ET)
ANY7_2_END_ET   = datetime(2025, 11, 30, 23, 59, 59, tzinfo=ET)

# ========== NEW MARKETS (2026) ==========
# 10.0+ before 2027
QUAKE_10_BEFORE_2027_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
QUAKE_10_BEFORE_2027_END_ET   = datetime(2026, 12, 31, 23, 59, 59, tzinfo=ET)

# 9.0+ before 2027
QUAKE_9_BEFORE_2027_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
QUAKE_9_BEFORE_2027_END_ET   = datetime(2026, 12, 31, 23, 59, 59, tzinfo=ET)

# Megaquake by January 31, 2026
MEGA_JAN31_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
MEGA_JAN31_END_ET   = datetime(2026, 1, 31, 23, 59, 59, tzinfo=ET)

# Megaquake by March 31, 2026
MEGA_MAR31_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
MEGA_MAR31_END_ET   = datetime(2026, 3, 31, 23, 59, 59, tzinfo=ET)

# Megaquake by June 30, 2026
MEGA_JUN30_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
MEGA_JUN30_END_ET   = datetime(2026, 6, 30, 23, 59, 59, tzinfo=ET)

# Another 7.0+ by March 31, 2026
ANY7_MAR31_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
ANY7_MAR31_END_ET   = datetime(2026, 3, 31, 23, 59, 59, tzinfo=ET)

# How many 7.0+ by June 30, 2026
COUNT_7_JUN30_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
COUNT_7_JUN30_END_ET   = datetime(2026, 6, 30, 23, 59, 59, tzinfo=ET)

# How many 6.5+ by January 11, 2026
COUNT_65_JAN11_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
COUNT_65_JAN11_END_ET   = datetime(2026, 1, 11, 23, 59, 59, tzinfo=ET)

# How many 6.5+ by January 18, 2026
COUNT_65_JAN18_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
COUNT_65_JAN18_END_ET   = datetime(2026, 1, 18, 23, 59, 59, tzinfo=ET)

# How many 7.0+ in 2026
COUNT_7_2026_START_ET = datetime(2026, 1, 1, 0, 0, 0, tzinfo=ET)
COUNT_7_2026_END_ET   = datetime(2026, 12, 31, 23, 59, 59, tzinfo=ET)

# Pending resolution window
PENDING_HOURS = 24
PENDING_FILE = "pending_markets.json"
SEEN_FILE = "seen_ids.json"

# Discord Configuration
DISCORD_WEBHOOK_URL = "https://discord.com/api/webhooks/1399905616478339222/_IexstbUDr9-_cvGllvwvhCaTt3iDs2qVGBIqrDPb4VPkNPA2fCWVtFdVLWLQDVt9zWh"  # Replace with your Discord webhook URL

# Polymarket Trading Configuration
POLYMARKET_PRIVATE_KEY = "0x3a08e6c54bbaee0fac8e3fdf7f8f0dc529e6744977610caf093e34e7cb4cd2f8"  # Replace with your wallet private key (0x...)
POLYMARKET_TRADE_AMOUNT_USD = 10.0  # Trade amount in USD
POLYGON_RPC_URL = "https://polygon-rpc.com"  # Polygon RPC endpoint
POLYMARKET_CLOB_API = "https://clob.polymarket.com"

# Market slug mapping (from labels to Polymarket slugs and outcome indices)
# Outcome index 0 = "Yes", 1 = "No" for binary markets
# For counting markets, outcome_index may need to be adjusted based on market structure
MARKET_MAPPING = {
    # ========== OLD MARKETS (2025) ==========
    "LA 50-mile ≥6.5 (2025-06-09..2025-12-31 23:59:59 ET)": {
        "slug": "magnitude-6pt5-earthquake-in-la-before-2026",
        "outcome_index": 0,  # Yes
    },
    "Megaquake ≥8.0 (2025-10-30..2025-11-30 23:59:59 ET)": {
        "slug": "megaquake-by-november-30-934",
        "outcome_index": 0,  # Yes
    },
    "Megaquake ≥8.0 (2025-09-30..2025-12-31 23:59:59 ET)": {
        "slug": "megaquake-by-december-31",
        "outcome_index": 0,  # Yes
    },
    "7.0+ anywhere (2025-10-30 19:00 ET..2025-11-15 23:59:59 ET)": {
        "slug": "another-7pt0-or-above-earthquake-by-october-31-951",
        "outcome_index": 0,  # November 15 outcome (Yes)
    },
    "7.0+ anywhere (2025-10-30 19:00 ET..2025-11-30 23:59:59 ET)": {
        "slug": "another-7pt0-or-above-earthquake-by-october-31-951",
        "outcome_index": 1,  # November 30 outcome (Yes) - Note: may need adjustment based on actual market structure
    },
    # ========== NEW MARKETS (2026) ==========
    "10.0+ earthquake before 2027": {
        "slug": "10pt0-or-above-earthquake-before-2027",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "9.0+ earthquake before 2027": {
        "slug": "9pt0-or-above-earthquake-before-2027",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "Megaquake by January 31, 2026": {
        "slug": "megaquake-by-january-31",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "Megaquake by March 31, 2026": {
        "slug": "megaquake-by-march-31",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "Megaquake by June 30, 2026": {
        "slug": "megaquake-by-june-30",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "Another 7.0+ earthquake by March 31, 2026": {
        "slug": "another-7pt0-or-above-earthquake-by-march-31",  # TODO: Update with actual slug
        "outcome_index": 0,  # Yes
    },
    "How many 7.0+ earthquakes by June 30, 2026": {
        "slug": "how-many-7pt0-or-above-earthquakes-by-june-30",  # TODO: Update with actual slug
        "outcome_index": 0,  # Note: Counting market - may need specific outcome index
    },
    "How many 6.5+ earthquakes by January 11, 2026": {
        "slug": "how-many-6pt5-or-above-earthquakes-by-january-11",  # TODO: Update with actual slug
        "outcome_index": 0,  # Note: Counting market - may need specific outcome index
    },
    "How many 6.5+ earthquakes by January 18, 2026": {
        "slug": "how-many-6pt5-or-above-earthquakes-by-january-18",  # TODO: Update with actual slug
        "outcome_index": 0,  # Note: Counting market - may need specific outcome index
    },
    "How many 7.0+ earthquakes in 2026": {
        "slug": "how-many-7pt0-or-above-earthquakes-in-2026",  # TODO: Update with actual slug
        "outcome_index": 0,  # Note: Counting market - may need specific outcome index
    },
}

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
log = logging.getLogger("eq-monitor-markets")


# ------------------ Utilities ------------------- #
def km_distance(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    R = 6371.0
    import math as m
    phi1, phi2 = m.radians(lat1), m.radians(lat2)
    dphi = m.radians(lat2 - lat1)
    dlmb = m.radians(lon2 - lon1)
    a = m.sin(dphi/2)**2 + m.cos(phi1)*m.cos(phi2)*m.sin(dlmb/2)**2
    c = 2 * m.atan2(m.sqrt(a), m.sqrt(1 - a))
    return R * c


def to_et(dt_utc: datetime) -> datetime:
    # Convert UTC -> ET (fixed UTC-4 for this script)
    return dt_utc.astimezone(ET)


def market_windows() -> Dict[str, Tuple[datetime, datetime]]:
    return {
        # Old markets (2025)
        "LA50_65": (LA_START_ET, LA_END_ET),
        "MEGA1_80": (MEGA1_START_ET, MEGA1_END_ET),
        "MEGA2_80": (MEGA2_START_ET, MEGA2_END_ET),
        "ANY7_1_70": (ANY7_1_START_ET, ANY7_1_END_ET),
        "ANY7_2_70": (ANY7_2_START_ET, ANY7_2_END_ET),
        # New markets (2026)
        "QUAKE_10_2027": (QUAKE_10_BEFORE_2027_START_ET, QUAKE_10_BEFORE_2027_END_ET),
        "QUAKE_9_2027": (QUAKE_9_BEFORE_2027_START_ET, QUAKE_9_BEFORE_2027_END_ET),
        "MEGA_JAN31": (MEGA_JAN31_START_ET, MEGA_JAN31_END_ET),
        "MEGA_MAR31": (MEGA_MAR31_START_ET, MEGA_MAR31_END_ET),
        "MEGA_JUN30": (MEGA_JUN30_START_ET, MEGA_JUN30_END_ET),
        "ANY7_MAR31": (ANY7_MAR31_START_ET, ANY7_MAR31_END_ET),
        "COUNT_7_JUN30": (COUNT_7_JUN30_START_ET, COUNT_7_JUN30_END_ET),
        "COUNT_65_JAN11": (COUNT_65_JAN11_START_ET, COUNT_65_JAN11_END_ET),
        "COUNT_65_JAN18": (COUNT_65_JAN18_START_ET, COUNT_65_JAN18_END_ET),
        "COUNT_7_2026": (COUNT_7_2026_START_ET, COUNT_7_2026_END_ET),
    }

def load_heartbeat_last() -> str | None:
    """Load the last heartbeat timestamp (YYYY-MM-DD-HH format)."""
    try:
        with open(HEARTBEAT_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data.get("last_timestamp") if isinstance(data, dict) else None
    except FileNotFoundError:
        return None
    except Exception:
        return None

def save_heartbeat_last(timestamp_str: str) -> None:
    """Save the last heartbeat timestamp (YYYY-MM-DD-HH format)."""
    try:
        with open(HEARTBEAT_FILE, "w", encoding="utf-8") as f:
            json.dump({"last_timestamp": timestamp_str}, f)
    except Exception:
        pass

def maybe_send_heartbeat():
    """
    Send once a day at HEARTBEAT_HOUR in HEARTBEAT_TZ.
    Uses HEARTBEAT_FILE to avoid duplicates.
    """
    tz = ZoneInfo(HEARTBEAT_TZ)
    now_local = datetime.now(timezone.utc).astimezone(tz)
    # Use hour+date to ensure we only send once per hour
    timestamp_str = now_local.strftime("%Y-%m-%d-%H")
    last = load_heartbeat_last()

    # Only send if:
    # 1. It's the right hour
    # 2. We're in the first 2 minutes (to catch the hour, but not too wide)
    # 3. We haven't sent in this hour yet (hour+date tracking prevents duplicates)
    if (now_local.hour == HEARTBEAT_HOUR and 
        now_local.minute < 2 and 
        last != timestamp_str):
        save_heartbeat_last(timestamp_str)  # Save first to prevent duplicates
        
        # Test USGS connection
        usgs_ok, usgs_msg = test_usgs_connection()
        
        # Build modern embed with color
        color = 0x00ff00 if usgs_ok else 0xff0000  # Green if OK, red if error
        status_emoji = "✅" if usgs_ok else "❌"
        
        embed = {
            "title": "💓 Earthquake Monitor Heartbeat",
            "description": f"Monitor is still running and active",
            "color": color,
            "fields": [
                {
                    "name": "⏰ Time",
                    "value": f"{now_local.strftime('%Y-%m-%d %H:%M')} ({HEARTBEAT_TZ})",
                    "inline": True
                },
                {
                    "name": f"{status_emoji} USGS API Status",
                    "value": usgs_msg.replace("✅ ", "").replace("❌ ", ""),
                    "inline": True
                }
            ],
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "footer": {
                "text": "Earthquake Monitor System"
            }
        }
        
        send_discord(content=None, embed=embed)


def in_window_et(dt_utc: datetime, start_et: datetime, end_et: datetime) -> bool:
    dt_et = to_et(dt_utc)
    return start_et <= dt_et <= end_et


def classify_markets(mag: float, lat: float, lon: float, t_utc: datetime) -> List[str]:
    """
    Classify which markets this earthquake matches.
    Returns list of market label strings.
    """
    labels: List[str] = []
    wins = market_windows()

    # ========== OLD MARKETS (2025) ==========
    # LA 50mi >= 6.5 within window
    if mag >= 6.5 and in_window_et(t_utc, *wins["LA50_65"]):
        if km_distance(lat, lon, LOS_ANGELES[0], LOS_ANGELES[1]) <= FIFTY_MILES_KM:
            labels.append("LA 50-mile ≥6.5 (2025-06-09..2025-12-31 23:59:59 ET)")

    # Megaquake 1: >= 8.0 between Oct 30 - Nov 30, 2025
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA1_80"]):
        labels.append("Megaquake ≥8.0 (2025-10-30..2025-11-30 23:59:59 ET)")

    # Megaquake 2: >= 8.0 between Sep 30 - Dec 31, 2025
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA2_80"]):
        labels.append("Megaquake ≥8.0 (2025-09-30..2025-12-31 23:59:59 ET)")

    # 7.0+ Rule 1: >= 7.0 between Oct 30 19:00 ET - Nov 15, 2025
    if mag >= 7.0 and in_window_et(t_utc, *wins["ANY7_1_70"]):
        labels.append("7.0+ anywhere (2025-10-30 19:00 ET..2025-11-15 23:59:59 ET)")

    # 7.0+ Rule 2: >= 7.0 between Oct 30 19:00 ET - Nov 30, 2025
    if mag >= 7.0 and in_window_et(t_utc, *wins["ANY7_2_70"]):
        labels.append("7.0+ anywhere (2025-10-30 19:00 ET..2025-11-30 23:59:59 ET)")

    # ========== NEW MARKETS (2026) ==========
    # 10.0+ before 2027
    if mag >= 10.0 and in_window_et(t_utc, *wins["QUAKE_10_2027"]):
        labels.append("10.0+ earthquake before 2027")

    # 9.0+ before 2027
    if mag >= 9.0 and in_window_et(t_utc, *wins["QUAKE_9_2027"]):
        labels.append("9.0+ earthquake before 2027")

    # Megaquake by January 31, 2026
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA_JAN31"]):
        labels.append("Megaquake by January 31, 2026")

    # Megaquake by March 31, 2026
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA_MAR31"]):
        labels.append("Megaquake by March 31, 2026")

    # Megaquake by June 30, 2026
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA_JUN30"]):
        labels.append("Megaquake by June 30, 2026")

    # Another 7.0+ by March 31, 2026
    if mag >= 7.0 and in_window_et(t_utc, *wins["ANY7_MAR31"]):
        labels.append("Another 7.0+ earthquake by March 31, 2026")

    # How many 7.0+ by June 30, 2026 (counting market)
    if mag >= 7.0 and in_window_et(t_utc, *wins["COUNT_7_JUN30"]):
        labels.append("How many 7.0+ earthquakes by June 30, 2026")

    # How many 6.5+ by January 11, 2026 (counting market)
    if mag >= 6.5 and in_window_et(t_utc, *wins["COUNT_65_JAN11"]):
        labels.append("How many 6.5+ earthquakes by January 11, 2026")

    # How many 6.5+ by January 18, 2026 (counting market)
    if mag >= 6.5 and in_window_et(t_utc, *wins["COUNT_65_JAN18"]):
        labels.append("How many 6.5+ earthquakes by January 18, 2026")

    # How many 7.0+ in 2026 (counting market)
    if mag >= 7.0 and in_window_et(t_utc, *wins["COUNT_7_2026"]):
        labels.append("How many 7.0+ earthquakes in 2026")

    return labels


def load_json_set(path: str) -> Set[str]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            arr = json.load(f)
            return set(arr) if isinstance(arr, list) else set()
    except FileNotFoundError:
        return set()
    except Exception as e:
        log.warning(f"Failed to read {path}: {e}")
        return set()


def save_json_set(path: str, s: Set[str]) -> None:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(sorted(list(s)), f, ensure_ascii=False, indent=2)
    except Exception as e:
        log.warning(f"Failed to write {path}: {e}")


def load_pending() -> Dict[str, Dict[str, Any]]:
    try:
        with open(PENDING_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except FileNotFoundError:
        return {}
    except Exception as e:
        log.warning(f"Failed to read {PENDING_FILE}: {e}")
        return {}


def save_pending(pending: Dict[str, Dict[str, Any]]) -> None:
    try:
        with open(PENDING_FILE, "w", encoding="utf-8") as f:
            json.dump(pending, f, ensure_ascii=False, indent=2, default=str)
    except Exception as e:
        log.warning(f"Failed to write {PENDING_FILE}: {e}")


def test_usgs_connection() -> Tuple[bool, str]:
    """
    Test connection to USGS API.
    Returns (success: bool, message: str)
    """
    try:
        # Make a simple test request with minimal parameters
        params = {
            "format": "geojson",
            "limit": "1",
        }
        r = requests.get(USGS_ENDPOINT, params=params, timeout=10)
        if r.status_code == 200:
            return True, f"✅ USGS API: Status {r.status_code} OK"
        else:
            return False, f"❌ USGS API: Status {r.status_code} (unexpected)"
    except requests.exceptions.Timeout:
        return False, "❌ USGS API: Connection timeout"
    except requests.exceptions.ConnectionError:
        return False, "❌ USGS API: Connection error (site may be blocked)"
    except Exception as e:
        return False, f"❌ USGS API: Error - {str(e)[:100]}"


def fetch_recent_events(since_utc: datetime) -> Dict[str, Any]:
    params = {
        "format": "geojson",
        "starttime": since_utc.replace(microsecond=0).isoformat(),
        "orderby": "time",
        "limit": "200",
    }
    r = requests.get(USGS_ENDPOINT, params=params, timeout=20)
    r.raise_for_status()
    return r.json()


def send_discord(content: str, embed: Dict[str, Any] | None = None) -> None:
    if not DISCORD_WEBHOOK_URL:
        log.error("DISCORD_WEBHOOK_URL not set")
        return
    payload: Dict[str, Any] = {"content": content}
    if embed:
        payload["embeds"] = [embed]
    resp = requests.post(DISCORD_WEBHOOK_URL, json=payload, timeout=20)
    if resp.status_code >= 300:
        log.error(f"Discord error {resp.status_code}: {resp.text[:300]}")


def build_embed(feature: Dict[str, Any], matched_labels: List[str], important: bool) -> Tuple[str, Dict[str, Any]]:
    p = feature.get("properties", {})
    g = feature.get("geometry", {}) or {}
    coords = g.get("coordinates", [None, None, None])
    lon, lat, depth_km = coords[0], coords[1], coords[2] if len(coords) > 2 else None

    mag = p.get("mag")
    place = p.get("place")
    time_ms = p.get("time")
    url = p.get("url") or p.get("detail")

    occurred_utc = datetime.fromtimestamp(time_ms / 1000, tz=timezone.utc) if time_ms else None
    et_str = to_et(occurred_utc).strftime("%Y-%m-%d %H:%M:%S ET") if occurred_utc else "N/A"

    title_prefix = "🚨 IMPORTANAT!!!!!!!" if important else "⚠️ Critical quake"
    title = f"{title_prefix} M{mag:.1f} earthquake"

    lines = []
    if matched_labels:
        lines.append("RELATED MARKETS:")
        for label in matched_labels:
            lines.append(f"• {label}")
    content = "\n".join(lines)

    embed = {
        "title": title,
        "url": url,
        "description": place or "Unknown location",
        "fields": [
            {"name": "Magnitude", "value": f"{mag:.1f}", "inline": True},
            {"name": "Time (ET)", "value": et_str, "inline": True},
            {"name": "Depth (km)", "value": f"{depth_km:.1f}" if depth_km is not None else "N/A", "inline": True},
            {"name": "Coordinates", "value": f"{lat:.4f}, {lon:.4f}", "inline": True},
        ],
    }
    return content, embed


def process_pending(pending: Dict[str, Dict[str, Any]]) -> None:
    """Optionally emit summary when items reach 24h. Here we just prune expired entries."""
    now_utc = datetime.now(timezone.utc)
    expired: List[str] = []
    for eid, rec in pending.items():
        expires_at = datetime.fromisoformat(rec["expires_at"])
        if now_utc >= expires_at:
            expired.append(eid)
    for eid in expired:
        pending.pop(eid, None)
    if expired:
        save_pending(pending)


def upsert_pending(pending: Dict[str, Dict[str, Any]], eid: str, mag: float, occurred_utc: datetime, labels: List[str]) -> None:
    now_utc = datetime.now(timezone.utc)
    expires = now_utc + timedelta(hours=PENDING_HOURS)
    rec = pending.get(eid)
    if rec:
        # update latest magnitude & labels union, push expiry forward from FIRST seen only
        rec["latest_mag"] = max(float(rec.get("latest_mag", 0.0)), float(mag))
        rec["labels"] = sorted(list(set(rec.get("labels", [])).union(labels)))
    else:
        pending[eid] = {
            "first_seen": now_utc.isoformat(),
            "occured_at": occurred_utc.isoformat(),
            "latest_mag": float(mag),
            "labels": labels,
            "expires_at": expires.isoformat(),
        }
    save_pending(pending)


# ------------------ Polymarket Trading Functions ------------------- #
def initialize_web3() -> Optional[Web3]:
    """Initialize Web3 connection to Polygon network."""
    try:
        w3 = Web3(Web3.HTTPProvider(POLYGON_RPC_URL))
        if not w3.is_connected():
            log.error("Failed to connect to Polygon RPC")
            return None
        return w3
    except Exception as e:
        log.error(f"Error initializing Web3: {e}")
        return None


def get_polymarket_market_info(slug: str) -> Optional[Dict[str, Any]]:
    """
    Fetch market information from Polymarket API by slug.
    Returns market data including condition ID and other identifiers.
    """
    endpoints_to_try = [
        (f"{POLYMARKET_CLOB_API}/markets/{slug}", None),
        (f"{POLYMARKET_CLOB_API}/markets", {"slug": slug}),
    ]
    
    for api_url, params in endpoints_to_try:
        try:
            response = requests.get(api_url, params=params, timeout=10)
            response.raise_for_status()
            data = response.json()
            
            # Handle different response formats
            markets = []
            if isinstance(data, list):
                markets = data
            elif isinstance(data, dict):
                if data.get('slug') == slug or data.get('questionId') or data.get('conditionId'):
                    return data
                if 'data' in data and isinstance(data['data'], list):
                    markets = data['data']
                else:
                    markets = [data]
            
            # Search through markets to find matching slug
            for market in markets:
                market_slug = market.get('slug') or market.get('marketSlug') or market.get('id')
                if market_slug and slug in market_slug:
                    log.info(f"Found matching market: {market.get('question', 'N/A')[:50]}")
                    return market
            
        except requests.exceptions.HTTPError as e:
            if e.response.status_code == 404:
                continue
            else:
                log.warning(f"HTTP error {e.response.status_code} from {api_url}: {e}")
                continue
        except Exception as e:
            log.warning(f"Error trying {api_url}: {e}")
            continue
    
    # Try GraphQL API as fallback
    try:
        graphql_url = "https://api.polymarket.com/graphql"
        query = """
        query GetMarket($slug: String!) {
            market(slug: $slug) {
                id
                slug
                question
                conditionId
                outcomes
            }
        }
        """
        variables = {"slug": slug}
        response = requests.post(
            graphql_url,
            json={"query": query, "variables": variables},
            timeout=10
        )
        if response.status_code == 200:
            graphql_data = response.json()
            if graphql_data.get('data', {}).get('market'):
                return graphql_data['data']['market']
    except Exception as e:
        log.warning(f"GraphQL API failed: {e}")
    
    log.error(f"All methods failed to find market with slug: {slug}")
    return None


def place_polymarket_order(market_label: str, eid: str, mag: float) -> Tuple[bool, str]:
    """
    Place a "Yes" buy order on Polymarket for the specified market.
    Returns (success: bool, message: str)
    """
    if not POLYMARKET_PRIVATE_KEY:
        return False, "POLYMARKET_PRIVATE_KEY not set in environment"
    
    if market_label not in MARKET_MAPPING:
        return False, f"Market label '{market_label}' not found in MARKET_MAPPING"
    
    market_info = MARKET_MAPPING[market_label]
    slug = market_info["slug"]
    outcome_index = market_info["outcome_index"]
    
    try:
        log.info(f"🚀 Starting trade for market: {slug} (label: {market_label})")
        
        # Step 1: Initialize Web3
        w3 = initialize_web3()
        if w3 is None:
            return False, "Failed to connect to Polygon network"
        
        # Step 2: Get account from private key
        account = Account.from_key(POLYMARKET_PRIVATE_KEY)
        address = account.address
        log.info(f"Account loaded: {address}")
        
        # Step 3: Get market info from Polymarket API
        market_data = get_polymarket_market_info(slug)
        if market_data is None:
            return False, f"Failed to fetch market information for slug: {slug}"
        
        # Step 4: Extract condition ID
        condition_id = (
            market_data.get('conditionId') or 
            market_data.get('condition_id') or
            market_data.get('id') or 
            market_data.get('questionId') or
            market_data.get('question_id')
        )
        
        if not condition_id:
            return False, f"Could not find condition ID in market response for {slug}"
        
        # Step 5: Calculate amount (USDC has 6 decimals)
        amount_raw = int(POLYMARKET_TRADE_AMOUNT_USD * 1e6)
        
        # Step 6: Get orderbook to find best price
        best_price = None
        try:
            token_id = f"{condition_id}_{outcome_index}"
            orderbook_url = f"{POLYMARKET_CLOB_API}/book"
            orderbook_params = {"token_id": token_id}
            
            orderbook_response = requests.get(orderbook_url, params=orderbook_params, timeout=10)
            if orderbook_response.status_code == 200:
                orderbook = orderbook_response.json()
                # Extract best ask price (price to buy)
                asks = orderbook.get('asks', [])
                if asks:
                    best_price = asks[0].get('price', '0.99')
                    log.info(f"Best ask price from orderbook: {best_price}")
        except Exception as e:
            log.warning(f"Could not fetch orderbook: {e}, using default price")
            best_price = "0.99"  # Default price if orderbook fails
        
        # Step 7: Prepare order data
        token_id = f"{condition_id}_{outcome_index}"
        order_data = {
            "token_id": token_id,
            "side": "BUY",
            "size": str(amount_raw),
            "price": str(best_price),
            "maker": address
        }
        
        log.info(f"Order data prepared: {json.dumps(order_data, indent=2)}")
        
        # Step 8: Note about EIP-712 signing requirement
        # Full execution requires EIP-712 signing and potentially API authentication
        # For now, we log the prepared order
        success_msg = (
            f"✅ Order prepared for market: {slug}\n"
            f"**Condition ID:** {condition_id}\n"
            f"**Token ID:** {token_id}\n"
            f"**Outcome Index:** {outcome_index} (Yes)\n"
            f"**Amount:** ${POLYMARKET_TRADE_AMOUNT_USD} ({amount_raw:,} raw units)\n"
            f"**Price:** {best_price}\n"
            f"**Account:** {address}\n\n"
            f"⚠️ **Note:** Order data prepared but full execution requires EIP-712 signing."
        )
        
        log.info(f"✅ Trade preparation complete for {slug}")
        return True, success_msg
        
    except Exception as e:
        error_msg = f"Error placing Polymarket order: {str(e)}"
        log.error(error_msg, exc_info=True)
        return False, error_msg


def execute_trades_for_markets(matched_labels: List[str], eid: str, mag: float) -> None:
    """
    Execute trades for all matched markets.
    Sends Discord notifications about trade attempts.
    """
    if not matched_labels:
        return
    
    if not POLYMARKET_PRIVATE_KEY:
        log.warning("POLYMARKET_PRIVATE_KEY not set, skipping trades")
        send_discord(
            content=f"⚠️ Market matches detected but trading disabled (POLYMARKET_PRIVATE_KEY not set)\n"
                   f"**Earthquake ID:** {eid}\n"
                   f"**Magnitude:** {mag:.1f}\n"
                   f"**Matched Markets:** {len(matched_labels)}\n"
                   f"• " + "\n• ".join(matched_labels)
        )
        return
    
    log.info(f"🎯 Executing trades for {len(matched_labels)} matched markets")
    
    trade_results = []
    for label in matched_labels:
        success, message = place_polymarket_order(label, eid, mag)
        trade_results.append({
            "label": label,
            "success": success,
            "message": message
        })
        
        # Send Discord notification for each trade attempt
        status_emoji = "✅" if success else "❌"
        send_discord(
            content=f"{status_emoji} **Trade Attempt: {label}**\n\n"
                   f"**Earthquake ID:** {eid}\n"
                   f"**Magnitude:** {mag:.1f}\n\n"
                   f"{message}"
        )
    
    # Summary notification
    successful = sum(1 for r in trade_results if r["success"])
    failed = len(trade_results) - successful
    
    summary = (
        f"📊 **Trade Execution Summary**\n\n"
        f"**Earthquake ID:** {eid}\n"
        f"**Magnitude:** {mag:.1f}\n"
        f"**Total Markets Matched:** {len(matched_labels)}\n"
        f"**Successful Preparations:** {successful}\n"
        f"**Failed:** {failed}\n\n"
    )
    
    if failed > 0:
        summary += "**Failed Markets:**\n"
        for r in trade_results:
            if not r["success"]:
                summary += f"• {r['label']}: {r['message']}\n"
    
    send_discord(content=summary)


def process_events(features: List[Dict[str, Any]], seen: Set[str], pending: Dict[str, Dict[str, Any]]) -> None:
    for feat in features:
        eid = feat.get("id")
        if not eid or eid in seen:
            continue

        p = feat.get("properties", {})
        g = feat.get("geometry", {}) or {}
        coords = g.get("coordinates", [None, None, None])
        lon, lat = coords[0], coords[1]
        mag = p.get("mag") or 0.0
        time_ms = p.get("time") or 0
        occurred_utc = datetime.fromtimestamp(time_ms / 1000, tz=timezone.utc)

        # Market classification (with windows in ET)
        labels = classify_markets(mag, lat, lon, occurred_utc)

        # Critical alert logic
        if mag >= CRITICAL_MAG:
            important = (mag >= 7.0) or bool(labels)
            content, embed = build_embed(feat, labels, important)
            send_discord(content=content, embed=embed)
            log.info(f"Alert sent for {eid} | M{mag} | labels={labels}")

        # If this touches any market, place it into pending for 24h revision window
        # and execute trades
        if labels:
            upsert_pending(pending, eid, mag, occurred_utc, labels)
            # Execute trades for all matched markets
            execute_trades_for_markets(labels, eid, mag)

        seen.add(eid)


def main() -> None:
    if not DISCORD_WEBHOOK_URL:
        log.error("Missing DISCORD_WEBHOOK_URL in .env")
        return

    try:
        # Send modern startup embed
        embed = {
            "title": "🚀 Earthquake Monitor Starting Up",
            "description": "Market-rule aware earthquake monitoring system initialized",
            "color": 0x00bfff,  # Bright blue for startup
            "fields": [
                {
                    "name": "📊 Monitor Type",
                    "value": "Market-Rule Aware",
                    "inline": True
                },
                {
                    "name": "⏰ Status",
                    "value": "Initializing...",
                    "inline": True
                }
            ],
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "footer": {
                "text": "Earthquake Monitor System"
            }
        }
        send_discord(content=None, embed=embed)
    except Exception as e:
        log.warning(f"Startup Discord ping failed: {e}")

    seen = load_json_set(SEEN_FILE)
    pending = load_pending()

    since_utc = datetime.now(timezone.utc) - timedelta(hours=LOOKBACK_HOURS)
    log.info("Starting market-rule-aware monitor")

    while True:
        try:
            data = fetch_recent_events(since_utc)
            feats = data.get("features", [])
            if feats:
                newest_ms = max(f.get("properties", {}).get("time", 0) for f in feats)
                since_utc = datetime.fromtimestamp(newest_ms / 1000, tz=timezone.utc) - timedelta(minutes=2)
            process_events(feats, seen, pending)
            save_json_set(SEEN_FILE, seen)
            process_pending(pending)
        except Exception as e:
            log.exception(f"Loop error: {e}")

        maybe_send_heartbeat()
        time.sleep(random.uniform(POLL_MIN_SEC, POLL_MAX_SEC))


if __name__ == "__main__":
    main()
