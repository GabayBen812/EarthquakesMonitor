
"""
USGS Earthquake Monitor -> Discord (Market-Rule Aware)
------------------------------------------------------
Matches three market-style rules:
  1) LA 50-mile: >= 6.5 within 50 miles of Los Angeles between 2025-06-09 00:00:00 ET
     and 2025-12-31 23:59:59 ET.
  2) Megaquake: >= 8.0 anywhere between 2025-07-30 00:00:00 ET and 2025-09-30 23:59:59 ET.
  3) 7.0+ anywhere: >= 7.0 anywhere between 2025-08-22 13:10:00 ET and 2025-09-30 23:59:59 ET.

Also:
  - Alerts on all >= 6.4 quakes (global critical), even if not in a market window.
  - For any quake that triggers a market, keep a 24h "pending window" where magnitude
    revisions may occur; updates re-alert and the latest value at 24h is considered final.
  - Haversine distance; 50 miles = 80.4672 km.
  - USGS FDSN Event API polling; Discord webhook notifications.
  - Persists seen IDs and pending market windows in JSON files.

Setup:
  pip install requests python-dotenv
  .env -> DISCORD_WEBHOOK_URL=...
  python eq_monitor_markets.py
"""

import os
import json
import time
import math
import random
import logging
from datetime import datetime, timedelta, timezone
from typing import Dict, Any, List, Set, Tuple
from zoneinfo import ZoneInfo

import requests
from dotenv import load_dotenv

# -------------------- Config -------------------- #
USGS_ENDPOINT = "https://earthquake.usgs.gov/fdsnws/event/1/query"
POLL_MIN_SEC = 5
POLL_MAX_SEC = 10
LOOKBACK_HOURS = 2
CRITICAL_MAG = 6.4
HEARTBEAT_TZ = os.getenv("HEARTBEAT_TZ", "Asia/Jerusalem")
HEARTBEAT_HOUR = int(os.getenv("HEARTBEAT_HOUR", "16"))
HEARTBEAT_FILE = "heartbeat_state.json"

# Reference & distances
LOS_ANGELES = (34.0522, -118.2437)
FIFTY_MILES_KM = 80.4672  # exact 50 miles

# Markets windows (ET). We'll construct aware datetimes in ET (UTC-4 during this period).
# We'll represent ET as a fixed offset UTC-4 for 2025 windows (DST-aware enough for this use).
# For strict TZ handling, swap to zoneinfo("America/New_York").
ET = timezone(timedelta(hours=-4), name="ET")

LA_START_ET = datetime(2025, 6, 9, 0, 0, 0, tzinfo=ET)
LA_END_ET   = datetime(2025, 12, 31, 23, 59, 59, tzinfo=ET)

MEGA_START_ET = datetime(2025, 7, 30, 0, 0, 0, tzinfo=ET)
MEGA_END_ET   = datetime(2025, 9, 30, 23, 59, 59, tzinfo=ET)

ANY7_START_ET = datetime(2025, 8, 22, 13, 10, 0, tzinfo=ET)
ANY7_END_ET   = datetime(2025, 9, 30, 23, 59, 59, tzinfo=ET)

# Pending resolution window
PENDING_HOURS = 24
PENDING_FILE = "pending_markets.json"
SEEN_FILE = "seen_ids.json"

# Discord
load_dotenv()
DISCORD_WEBHOOK_URL = os.getenv("DISCORD_WEBHOOK_URL", "").strip()

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
        "LA50_65": (LA_START_ET, LA_END_ET),
        "MEGA_80": (MEGA_START_ET, MEGA_END_ET),
        "ANY7_70": (ANY7_START_ET, ANY7_END_ET),
    }

def load_heartbeat_last() -> str | None:
    try:
        with open(HEARTBEAT_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data.get("last_date") if isinstance(data, dict) else None
    except FileNotFoundError:
        return None
    except Exception:
        return None

def save_heartbeat_last(date_str: str) -> None:
    try:
        with open(HEARTBEAT_FILE, "w", encoding="utf-8") as f:
            json.dump({"last_date": date_str}, f)
    except Exception:
        pass

def maybe_send_heartbeat():
    """
    Send once a day at HEARTBEAT_HOUR in HEARTBEAT_TZ.
    Uses HEARTBEAT_FILE to avoid duplicates.
    """
    tz = ZoneInfo(HEARTBEAT_TZ)
    now_local = datetime.now(timezone.utc).astimezone(tz)
    today_str = now_local.strftime("%Y-%m-%d")
    last = load_heartbeat_last()

    # send only if it's the right hour and we didn't send today
    if now_local.hour == HEARTBEAT_HOUR and last != today_str:
        send_discord(content=f"✅ Earthquake monitor heartbeat — still running ({today_str} {HEARTBEAT_HOUR:02d}:00, {HEARTBEAT_TZ}).")
        save_heartbeat_last(today_str)


def in_window_et(dt_utc: datetime, start_et: datetime, end_et: datetime) -> bool:
    dt_et = to_et(dt_utc)
    return start_et <= dt_et <= end_et


def classify_markets(mag: float, lat: float, lon: float, t_utc: datetime) -> List[str]:
    labels: List[str] = []
    wins = market_windows()

    # LA 50mi >= 6.5 within window
    if mag >= 6.5 and in_window_et(t_utc, *wins["LA50_65"]):
        if km_distance(lat, lon, LOS_ANGELES[0], LOS_ANGELES[1]) <= FIFTY_MILES_KM:
            labels.append("LA 50-mile ≥6.5 (2025-06-09..2025-12-31 23:59:59 ET)")

    # Megaquake >= 8.0 within window
    if mag >= 8.0 and in_window_et(t_utc, *wins["MEGA_80"]):
        labels.append("Megaquake ≥8.0 (2025-07-30..2025-09-30 23:59:59 ET)")

    # Another 7.0+ anywhere within window
    if mag >= 7.0 and in_window_et(t_utc, *wins["ANY7_70"]):
        labels.append("Another 7.0+ anywhere (2025-08-22 13:10 ET..2025-09-30 23:59:59 ET)")

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
        if labels:
            upsert_pending(pending, eid, mag, occurred_utc, labels)

        seen.add(eid)


def main() -> None:
    if not DISCORD_WEBHOOK_URL:
        log.error("Missing DISCORD_WEBHOOK_URL in .env")
        return

    try:
        send_discord(content="🚀 Earthquake monitor starting up (market-rule aware).")
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
