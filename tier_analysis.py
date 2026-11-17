#!/usr/bin/env python3
"""
tier_analysis.py - tune Unveil's place-rarity tiers against real OpenStreetMap data.

WHAT IT DOES
    1. Fetches places around a point from Overpass (cached to disk).
    2. Scores every place with `score_place()` and assigns a tier (1-4 stars).
    3. Prints a report so you can SEE whether the weights make sense:
         - how many places land in each tier
         - which kinds of places land where (crosstab)
         - how often useful OSM tags exist (wikidata, name:en, website...)
         - the highest / lowest examples inside each tier (the boundary cases)
         - how many markers a phone screen would show at each zoom level
         - JRPG town cells: one building per category per town, landmarks always shown,
           the rest become '?' secrets (and how crowded or empty the screen looks)
         - how far the nearest konbini/supermarket is (for the hydration reminder)
         - how much the app's CURRENT Overpass query misses

HOW TO RUN (WSL, no installs needed - standard library only)
    python3 tier_analysis.py                     # central Kobe, 2 km radius
    python3 tier_analysis.py --examples 30       # longer example lists
    python3 tier_analysis.py --out report.txt    # also save the report
    python3 tier_analysis.py --refresh           # ignore the cache, refetch

    The first run downloads data and saves it to overpass_cache.json, so tuning
    the weights below and re-running is instant and doesn't hit the public
    Overpass server again.

THE LOOP
    run -> read report -> edit weights in the CONFIG section -> run again.

The scoring logic is a pure function (no network, no globals mutated), which is
why it is easy to test. See test_tier_analysis.py.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import re
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

# =============================================================================
# CONFIG - everything you will want to tune lives in this section
# =============================================================================

DEFAULT_CENTER = (34.6901, 135.1956)  # central Kobe, same as DEFAULT_POSITION in App.jsx
DEFAULT_RADIUS_M = 2000
OVERPASS_URL = "https://overpass-api.de/api/interpreter"
SCRIPT_VERSION = "0.6 (suburban categories, overworld icons)"
USER_AGENT = "unveil-tier-analysis/0.6 (personal learning project)"

# What we ask Overpass for. Deliberately a bit broader than the app's list, and
# every value is matched EXACTLY (anchored regex) instead of "contains".
FETCH_FILTERS: dict[str, list[str]] = {
    "amenity": [
        "cafe", "restaurant", "bar", "pub", "fast_food", "ice_cream", "library",
        "cinema", "theatre", "marketplace", "community_centre",
        "place_of_worship",  # <- where most Japanese shrines and temples live
        "public_bath",       # sento
        "post_office", "townhall", "pharmacy",   # the civic buildings every town has
        "drinking_water",    # supply layer (hydration), never a town building
    ],
    "leisure": ["park", "garden", "sports_centre", "playground", "nature_reserve"],
    "tourism": ["museum", "attraction", "viewpoint", "gallery", "artwork", "zoo", "aquarium",
                "hotel", "guest_house", "hostel"],  # lodging -> 宿屋
    "shop": ["bakery", "books", "supermarket", "convenience"],
    "historic": [
        "monument", "castle", "ruins", "memorial", "archaeological_site",
        "building", "city_gate", "wayside_shrine", "shrine", "temple",
    ],
    "railway": ["station", "halt"],
    "natural": ["peak", "spring"],
    "waterway": ["waterfall"],
}

# The app's CURRENT query (INTERESTING_TYPES in overpassService.js), used only
# to measure what it misses. The app matches these as unanchored regexes on
# nodes only.
APP_CURRENT_TYPES: dict[str, list[str]] = {
    "amenity": ["cafe", "restaurant", "bar", "pub", "fast_food", "ice_cream",
                "library", "cinema", "theatre", "marketplace", "community_centre"],
    "leisure": ["park", "garden", "sports_centre", "playground", "nature_reserve"],
    "tourism": ["museum", "attraction", "viewpoint", "gallery", "artwork",
                "information", "zoo", "aquarium"],
    "shop": ["bakery", "books", "supermarket", "convenience"],
    "historic": ["monument", "castle", "temple", "shrine", "ruins", "memorial"],
}

# Base points by KIND of place. Unknown kinds get DEFAULT_BASE.
BASE_POINTS: dict[str, int] = {
    # With the tier-2 threshold at 12, any kind whose base is below 12 needs at least
    # one REAL signal (name:en, website, ...) before it is visible. That is deliberate:
    # a plain restaurant is not interesting, a documented one might be.
    "castle": 40, "zoo": 25, "aquarium": 25,
    "shrine": 20, "temple": 20, "attraction": 20, "museum": 20,
    "gallery": 15, "garden": 15, "nature_reserve": 15, "viewpoint": 15,
    "theatre": 12, "archaeological_site": 12, "park": 12, "public_bath": 12, "monument": 12, "ruins": 12,
    "city_gate": 12, "library": 12, "cafe": 12, "bakery": 12,
    "ice_cream": 10, "cinema": 10, "marketplace": 10,
    "restaurant": 8, "bar": 8, "pub": 8, "place_of_worship": 8,
    "artwork": 6, "books": 6, "memorial": 6,
    "fast_food": 5, "wayside_shrine": 5, "building": 5, "sports_centre": 5,
    "community_centre": 3, "playground": 3, "memorial_minor": 2,
    "supermarket": 0, "convenience": 0, "hotel": 0,
    "inn": 15, "church": 12,
    "station": 15, "townhall": 15, "post_office": 12, "pharmacy": 8,
    "peak": 15, "waterfall": 15, "spring": 10, "drinking_water": 0,
}
DEFAULT_BASE = 3

# Extra points when mappers cared enough to add these tags. Tag richness is our
# stand-in for "this place matters".
SIGNAL_POINTS: dict[str, int] = {
    "wikidata": 30,   # a Wikidata entry alone makes a place notable...
    "wikipedia": 20,  # ...an actual Wikipedia article makes it a landmark
    "heritage": 20,
    "name:en": 5,
    "website": 5,
    "description": 5,
    "start_date": 5,
    "opening_hours": 2,
}

# Big green spaces deserve a bonus (largest threshold first, only one applies).
AREA_KINDS = {"park", "garden", "nature_reserve", "sports_centre"}
AREA_BONUS = [(100_000, 15), (20_000, 8)]  # (minimum m^2, bonus points)

# Chain detection. Each signal has its own penalty because they differ in certainty.
CHAIN_PENALTIES = {
    "brand tag": -30,
    "known chain": -30,
    "repeated name": -20,
    "branch-style name": -15,
}
CHAIN_TAG_KEYS = ("brand", "brand:wikidata", "brand:en", "brand:ja")
CHAIN_REPEAT_MIN = 3  # same name this many times in the fetched area => probably a chain
CHAIN_NAME_RE = re.compile(
    r"セブン|ローソン|ファミリーマート|ミニストップ|スターバックス|ドトール|タリーズ|"
    r"マクドナルド|モスバーガー|ケンタッキー|すき家|吉野家|松屋|サイゼリヤ|ガスト|"
    r"コメダ|ミスタードーナツ|ロッテリア|CoCo壱番屋|イオン|ダイエー|コープ|"
    r"なか卯|スシロー|くら寿司|はま寿司|ジョリーパスタ|大戸屋|餃子の王将|天下一品|"
    r"やよい軒|ココス|バーミヤン|丸亀製麺|はなまる|日高屋|一風堂|牛角|やきとり大吉|"
    r"東横INN|東横イン|スーパーホテル|アパホテル|ルートイン|ドーミーイン|ダイワロイネット|"
    r"7-?Eleven|Seven-?Eleven|Lawson|FamilyMart|Starbucks|McDonald|Doutor|Tully",
    re.IGNORECASE,
)
# "Name 元町店", "Name 三宮店（2号店）": a space, then a branch name ending in 店.
BRANCH_NAME_RE = re.compile(r"\s\S+店(?:[（(].*[）)])?$")
# Repeated-name and branch-name heuristics only make sense for businesses. Many
# different shrines are legitimately called 稲荷神社, and that is not a chain.
COMMERCIAL_KINDS = {"restaurant", "cafe", "bar", "pub", "fast_food", "bakery", "ice_cream",
                    "convenience", "supermarket", "books", "cinema", "hotel"}
# Plaques, stones and benches are everywhere and rarely worth a trip.
MINOR_MEMORIALS = {"plaque", "stone", "bench", "stolperstein", "ghost_bike", "tree"}
# Institutions that are "chains" on paper but are one-per-town in the story world.
CHAIN_EXEMPT_KINDS = {"post_office", "townhall", "station", "pharmacy"}
# A tourism=hotel whose name looks like a traditional inn is treated as a 宿屋 (inn).
RYOKAN_NAME_RE = re.compile(r"旅館|旅荘|荘$|庵|の宿|民宿")

# (minimum points, tier), checked top-down. Anything below the last is tier 1.
TIER_THRESHOLDS = [(55, 4), (25, 3), (12, 2)]
TIER_LABELS = {1: "common", 2: "local", 3: "notable", 4: "landmark"}

EARTH_M_PER_DEG = 111_320  # metres per degree of latitude (rough, fine here)

# --- Town system: the JRPG "one inn, one item shop" rule ----------------------------------
# Mirrors the vocabulary in themes.js (keep the two in sync, or move both to one JSON file).
# Places sharing a themed name compete for ONE slot per town cell. Kinds that are not
# listed here can never be town buildings.
THEMED_NAMES: dict[str, str] = {
    "cafe": "茶屋", "bar": "酒場", "pub": "酒場",
    "restaurant": "食事処", "fast_food": "街道の屋台", "ice_cream": "甘味処",
    "bakery": "パン職人の店",
    "library": "書庫", "books": "古書堂", "museum": "遺物館", "gallery": "展示館",
    "cinema": "集会堂", "theatre": "芝居小屋", "community_centre": "寄合所",
    "marketplace": "市場",
    "park": "森の広場", "garden": "妖精の庭園", "nature_reserve": "聖なる森",
    "playground": "子らの遊び場", "sports_centre": "修練場", "viewpoint": "見晴らし台",
    "shrine": "古き社", "temple": "神殿", "church": "教会", "place_of_worship": "小さな祠",
    "wayside_shrine": "小さな祠",
    "monument": "石碑", "memorial": "慰霊碑", "castle": "城塞",
    "ruins": "古代遺跡", "archaeological_site": "古代遺跡", "city_gate": "城門",
    "building": "古き館", "attraction": "名所", "artwork": "古の像",
    "zoo": "獣の園", "aquarium": "水の宮", "public_bath": "癒しの湯",
    "inn": "宿屋", "hotel": "宿屋",
    "post_office": "飛脚屋", "station": "宿場", "townhall": "役所", "pharmacy": "薬屋",
    "peak": "霊峰", "spring": "名水", "waterfall": "滝",
}
# 道具屋: konbini and supermarkets are a SUPPLY layer (nearest one, on demand, e.g. for the
# hydration reminder). They never take a town slot, and chains are exactly what we want.
UTILITY_KINDS = {"convenience", "supermarket", "drinking_water"}
TOWN_LIMITS = [20, 40, 80]   # a tile with more than this many buildings-to-be splits in four
ROOT_ZOOM, MAX_ZOOM = 15, 18  # about 1 km down to about 125 m at Kobe's latitude
SENSE_RADIUS_M = 40          # a "?" appears when a secret is this close


# =============================================================================
# DATA SHAPES
# =============================================================================

@dataclass
class Place:
    key: str                 # "node/123", "way/456", "relation/789"
    lat: float
    lng: float
    name: str | None
    kind: str
    tags: dict
    area_m2: float | None = None

    @property
    def osm_type(self) -> str:
        return self.key.split("/")[0]


@dataclass
class Scored:
    place: Place
    points: int
    tier: int
    reasons: list[str] = field(default_factory=list)
    chain: bool = False


# =============================================================================
# PURE LOGIC - no network, no files. This is the part worth unit-testing.
# =============================================================================

def classify(tags: dict) -> str:
    """Turn raw OSM tags into one 'kind' string (shrine, cafe, park, ...)."""
    if tags.get("amenity") == "place_of_worship":
        religion = tags.get("religion")
        if religion == "shinto":
            return "shrine"
        if religion == "buddhist":
            return "temple"
        if religion == "christian":
            return "church"
        return "place_of_worship"  # Jizo statues, tiny roadside sites: the 小さな祠 slot
    if tags.get("historic") in FETCH_FILTERS["historic"]:
        if tags["historic"] == "memorial" and tags.get("memorial") in MINOR_MEMORIALS:
            return "memorial_minor"
        return tags["historic"]
    if tags.get("railway") in FETCH_FILTERS["railway"]:
        return "station"
    if tags.get("natural") in FETCH_FILTERS["natural"]:
        return tags["natural"]
    if tags.get("waterway") in FETCH_FILTERS["waterway"]:
        return tags["waterway"]
    tourism = tags.get("tourism")
    if tourism == "guest_house":  # ryokan, minshuku, pensions live here in Japanese OSM
        return "inn"
    if tourism in ("hotel", "hostel"):
        name = tags.get("name") or tags.get("name:ja") or ""
        return "inn" if tourism == "hotel" and RYOKAN_NAME_RE.search(name) else "hotel"
    for key in ("tourism", "leisure", "amenity", "shop"):
        if tags.get(key) in FETCH_FILTERS[key]:
            return tags[key]
    return "other"


def has_signal(tags: dict, signal: str) -> bool:
    if signal == "website":
        return any(tags.get(k) for k in ("website", "contact:website", "url"))
    if signal == "heritage":
        return any(k == "heritage" or k.startswith("heritage:") for k in tags)
    return bool(tags.get(signal))


def chain_signal(tags: dict, name: str | None, kind: str,
                 name_counts: Counter | None = None) -> str | None:
    """Return WHY we think this is a chain (a key of CHAIN_PENALTIES), or None."""
    if kind in CHAIN_EXEMPT_KINDS:
        return None
    if any(k in tags for k in CHAIN_TAG_KEYS):
        return "brand tag"
    if not name:
        return None
    if CHAIN_NAME_RE.search(name):
        return "known chain"
    if kind in COMMERCIAL_KINDS:
        if name_counts and name_counts.get(name, 0) >= CHAIN_REPEAT_MIN:
            return "repeated name"
        if BRANCH_NAME_RE.search(name):
            return "branch-style name"
    return None


def tier_for(points: int) -> int:
    for minimum, tier in TIER_THRESHOLDS:
        if points >= minimum:
            return tier
    return 1


def score_place(place: Place, overrides: dict[str, int] | None = None,
                name_counts: Counter | None = None) -> Scored:
    """Score one place. `overrides` maps "node/123" -> minimum tier.
    `name_counts` (name -> occurrences in the area) powers the repeated-name chain check."""
    base = BASE_POINTS.get(place.kind, DEFAULT_BASE)
    points = base
    reasons = [f"base {base}"]

    for signal, bonus in SIGNAL_POINTS.items():
        if has_signal(place.tags, signal):
            points += bonus
            reasons.append(f"+{bonus} {signal}")

    if place.kind in AREA_KINDS and place.area_m2:
        for threshold, bonus in AREA_BONUS:
            if place.area_m2 >= threshold:
                points += bonus
                reasons.append(f"+{bonus} area>={threshold // 1000}k m2")
                break

    why = chain_signal(place.tags, place.name, place.kind, name_counts)
    if why:
        penalty = CHAIN_PENALTIES[why]
        points += penalty
        reasons.append(f"{penalty} chain ({why})")

    tier = tier_for(points)

    if not place.name:  # nothing to show on a quest card
        tier = 1
        reasons.append("unnamed -> hidden")

    if overrides and place.key in overrides and overrides[place.key] > tier:
        tier = overrides[place.key]
        reasons.append(f"override -> tier {tier}")

    return Scored(place, points, tier, reasons, chain=bool(why))


def matches_current_app_query(place: Place) -> bool:
    """Would the app's CURRENT Overpass query have found this place?

    The app asks for nodes only and uses unanchored regexes, so we mimic both.
    """
    if place.osm_type != "node":
        return False
    for key, values in APP_CURRENT_TYPES.items():
        value = place.tags.get(key)
        if value and re.search("|".join(values), value):
            return True
    return False


# ---- geometry helpers --------------------------------------------------------

def _offset_m(lat: float, lng: float, lat0: float, lng0: float) -> tuple[float, float]:
    """(east, north) offset in metres of a point from a reference point."""
    cos_lat = math.cos(math.radians(lat0))
    return (lng - lng0) * EARTH_M_PER_DEG * cos_lat, (lat - lat0) * EARTH_M_PER_DEG


def _distance_m(a: Place, b: Place) -> float:
    dx, dy = _offset_m(a.lat, a.lng, b.lat, b.lng)
    return math.hypot(dx, dy)


def _bbox_area_m2(bounds: dict) -> float:
    mid_lat = (bounds["minlat"] + bounds["maxlat"]) / 2
    height = (bounds["maxlat"] - bounds["minlat"]) * EARTH_M_PER_DEG
    width = (bounds["maxlon"] - bounds["minlon"]) * EARTH_M_PER_DEG * math.cos(math.radians(mid_lat))
    return abs(width * height)  # bounding box: overestimates diagonal shapes, fine for a bonus


def parse_elements(elements: list[dict]) -> list[Place]:
    """Raw Overpass elements -> Place objects (skips anything we can't locate)."""
    places: list[Place] = []
    for el in elements:
        tags = el.get("tags") or {}
        area = None
        if "lat" in el and "lon" in el:
            lat, lng = el["lat"], el["lon"]
        elif "bounds" in el:
            b = el["bounds"]
            lat, lng = (b["minlat"] + b["maxlat"]) / 2, (b["minlon"] + b["maxlon"]) / 2
            area = _bbox_area_m2(b)
        else:
            continue
        places.append(Place(
            key=f"{el['type']}/{el['id']}",
            lat=lat, lng=lng,
            name=tags.get("name") or tags.get("name:ja"),
            kind=classify(tags),
            tags=tags,
            area_m2=area,
        ))
    return places


def dedupe(places: list[Place], within_m: float = 50) -> list[Place]:
    """Drop duplicates: same name within `within_m` metres (e.g. a shrine mapped
    as both a node and a building outline). Keeps the one with the most tags."""
    kept: list[Place] = []
    seen_by_name: dict[str, list[Place]] = defaultdict(list)
    for p in sorted(places, key=lambda p: -len(p.tags)):
        if p.name:
            if any(_distance_m(p, q) <= within_m for q in seen_by_name[p.name]):
                continue
            seen_by_name[p.name].append(p)
        kept.append(p)
    return kept


# =============================================================================
# TOWN SYSTEM  (the "one inn, one item shop" rule, scaled up to big cities)
# =============================================================================

Cell = tuple[int, int, int]  # (zoom, tile x, tile y)


def themed_name(kind: str) -> str | None:
    return THEMED_NAMES.get(kind)


def slot_eligible(s: Scored) -> bool:
    """Can this place be a building in a JRPG town? (named, not a chain, not a supply
    point, and its kind has an in-world name)"""
    return bool(s.place.name and not s.chain and s.place.kind not in UTILITY_KINDS
                and themed_name(s.place.kind))


def rank_key(s: Scored) -> tuple[int, int, str]:
    """Total order for picking winners. The final key tie-break makes it deterministic,
    so every player sees the same town."""
    return (s.points, len(s.place.tags), s.place.key)


def tile_of(lat: float, lng: float, zoom: int) -> tuple[int, int]:
    """Web-mercator tile (x, y) containing a point: the same grid every web map uses."""
    n = 2 ** zoom
    x = int((lng + 180.0) / 360.0 * n)
    y = int((1.0 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2.0 * n)
    return x, y


def cell_size_m(zoom: int, lat: float) -> float:
    return 40_075_016 * math.cos(math.radians(lat)) / 2 ** zoom


def assign_cells(items: list[Scored], root_zoom: int, max_zoom: int, limit: int) -> dict[str, Cell]:
    """Adaptive town cells (a quadtree). Start with big tiles; any tile holding more than
    `limit` places splits into its four children, down to `max_zoom`.
    Returns {place key: the leaf tile it ended up in}."""
    cells: dict[str, Cell] = {}

    def split(zoom: int, bucket: list[Scored]) -> None:
        if zoom >= max_zoom or len(bucket) <= limit:  # base case: this tile is one town
            for s in bucket:
                cells[s.place.key] = (zoom, *tile_of(s.place.lat, s.place.lng, zoom))
            return
        children: dict[tuple[int, int], list[Scored]] = defaultdict(list)
        for s in bucket:
            children[tile_of(s.place.lat, s.place.lng, zoom + 1)].append(s)
        for child_bucket in children.values():
            split(zoom + 1, child_bucket)

    roots: dict[tuple[int, int], list[Scored]] = defaultdict(list)
    for s in items:
        roots[tile_of(s.place.lat, s.place.lng, root_zoom)].append(s)
    for bucket in roots.values():
        split(root_zoom, bucket)
    return cells


def pick_shown(items: list[Scored], cells: dict[str, Cell]) -> dict[str, Scored]:
    """Which places appear on the map? Landmarks (4 stars) always. Everything else: only the
    best place per (town cell, themed name). Returns {place key: Scored}."""
    best: dict[tuple[Cell, str], Scored] = {}
    for s in items:
        slot = (cells[s.place.key], themed_name(s.place.kind))
        if slot not in best or rank_key(s) > rank_key(best[slot]):
            best[slot] = s
    shown = {s.place.key: s for s in best.values()}
    for s in items:
        if s.tier == 4:
            shown[s.place.key] = s
    return shown


# =============================================================================
# NETWORK + CACHE
# =============================================================================

def build_query(lat: float, lng: float, radius: int) -> str:
    lines = []
    for key, values in FETCH_FILTERS.items():
        pattern = "|".join(values)
        lines.append(f'  nwr["{key}"~"^({pattern})$"](around:{radius},{lat},{lng});')
    body = "\n".join(lines)
    # "bb" gives nodes their lat/lon and ways/relations a bounding box (for area).
    return f"[out:json][timeout:90];\n(\n{body}\n);\nout tags bb;"


def fetch_overpass(query: str, url: str, attempts: int = 3) -> dict:
    payload = urllib.parse.urlencode({"data": query}).encode()
    request = urllib.request.Request(url, data=payload, headers={"User-Agent": USER_AGENT})
    for attempt in range(attempts):
        try:
            with urllib.request.urlopen(request, timeout=120) as response:
                return json.load(response)
        except urllib.error.HTTPError as err:
            retriable = err.code in (429, 502, 503, 504)
            if not retriable or attempt == attempts - 1:
                raise
        except urllib.error.URLError:
            if attempt == attempts - 1:
                raise
        wait = 5 * 2 ** attempt
        print(f"[overpass] busy, retrying in {wait}s (attempt {attempt + 2}/{attempts})...",
              file=sys.stderr)
        time.sleep(wait)
    raise RuntimeError("unreachable")


def load_elements(args: argparse.Namespace) -> list[dict]:
    query = build_query(args.lat, args.lng, args.radius)
    params = {"lat": args.lat, "lng": args.lng, "radius": args.radius,
              "query": hashlib.sha1(query.encode()).hexdigest()[:12]}  # filters changed -> refetch
    cache = Path(args.cache)
    if cache.exists() and not args.refresh:
        saved = json.loads(cache.read_text(encoding="utf-8"))
        if saved.get("params") == params:
            print(f"[cache] using {cache}", file=sys.stderr)
            return saved["elements"]
        print("[cache] parameters changed, refetching", file=sys.stderr)

    print(f"[overpass] fetching radius {args.radius} m around {args.lat}, {args.lng}...",
          file=sys.stderr)
    data = fetch_overpass(query, args.endpoint)
    elements = data.get("elements", [])
    cache.write_text(json.dumps({"params": params, "elements": elements}, ensure_ascii=False),
                     encoding="utf-8")
    print(f"[overpass] got {len(elements)} elements, cached to {cache}", file=sys.stderr)
    return elements


# =============================================================================
# REPORTS
# =============================================================================

def stars(tier: int) -> str:
    return "★" * tier


def report_summary(emit, scored: list[Scored]) -> None:
    total = len(scored)
    unnamed = sum(1 for s in scored if not s.place.name)
    emit(f"TIER SUMMARY  ({total} places after de-duplication, {unnamed} unnamed)")
    counts = Counter(s.tier for s in scored)
    for tier in (1, 2, 3, 4):
        n = counts[tier]
        emit(f"  {stars(tier):<5} {TIER_LABELS[tier]:<9} {n:>6}  ({100 * n / max(total, 1):4.1f}%)")
    emit()


def report_crosstab(emit, scored: list[Scored]) -> None:
    emit("KIND x TIER  (does each kind of place land where you expect?)")
    by_kind: dict[str, Counter] = defaultdict(Counter)
    for s in scored:
        by_kind[s.place.kind][s.tier] += 1
    emit(f"  {'kind':<20}{'total':>6}{'1★':>7}{'2★':>7}{'3★':>7}{'4★':>7}")
    for kind, counter in sorted(by_kind.items(), key=lambda kv: -sum(kv[1].values())):
        emit(f"  {kind:<20}{sum(counter.values()):>6}"
             f"{counter[1]:>7}{counter[2]:>7}{counter[3]:>7}{counter[4]:>7}")
    emit()


def report_signals(emit, scored: list[Scored], top_kinds: int = 12) -> None:
    emit("TAG COVERAGE  (% of NAMED places in each kind that have the tag)")
    signals = ["wikidata", "wikipedia", "name:en", "website", "opening_hours", "heritage"]
    emit(f"  {'kind':<20}{'named':>6}" + "".join(f"{s[:9]:>11}" for s in signals) + f"{'chain':>8}")
    kinds = Counter(s.place.kind for s in scored if s.place.name)
    for kind, n in kinds.most_common(top_kinds):
        group = [s for s in scored if s.place.kind == kind and s.place.name]
        cells = "".join(
            f"{100 * sum(has_signal(s.place.tags, sig) for s in group) / n:>10.0f}%" for sig in signals
        )
        chain_pct = 100 * sum(any("chain" in r for r in s.reasons) for s in group) / n
        emit(f"  {kind:<20}{n:>6}{cells}{chain_pct:>7.0f}%")
    emit()


def _format_example(s: Scored) -> str:
    why = ", ".join(s.reasons[1:])
    return f"  {s.points:>4}  {s.place.kind:<16} {s.place.name or '(unnamed)'}   [{why}]"


def report_examples(emit, scored: list[Scored], n: int) -> None:
    emit(f"EXAMPLES PER TIER  (top {n} and bottom {n}; the edges show where thresholds bite)")
    for tier in (4, 3, 2, 1):
        group = sorted(
            (s for s in scored if s.tier == tier and (tier > 1 or s.place.name)),
            key=lambda s: (-s.points, s.place.name or ""),
        )
        emit(f"\n{stars(tier)} {TIER_LABELS[tier]}  ({len(group)} named places)")
        emit("  highest:")
        for s in group[:n]:
            emit(_format_example(s))
        remaining = group[n:]  # never repeat what "highest" already showed
        if tier > 1 and remaining:
            emit("  lowest:")
            for s in remaining[::-1][:n]:
                emit(_format_example(s))
    emit()


def _viewport(zoom: int, lat0: float, screen: tuple[int, int]) -> tuple[float, float, float]:
    """(metres per pixel, half width m, half height m) of a phone screen at a zoom level."""
    m_per_px = 156_543.03392 * math.cos(math.radians(lat0)) / 2 ** zoom
    return m_per_px, screen[0] * m_per_px / 2, screen[1] * m_per_px / 2


def _land_predicate(points: list[tuple[float, float]], near: float):
    """A cheap land mask: True for spots within `near` metres of any known place, so harbours
    and mountains don't count as "empty screens". Returns None (no mask) when near <= 0."""
    if near <= 0:
        return None
    grid: dict[tuple[int, int], list[tuple[float, float]]] = defaultdict(list)
    for x, y in points:
        grid[(int(x // near), int(y // near))].append((x, y))

    def keep(px: float, py: float) -> bool:
        gx, gy = int(px // near), int(py // near)
        return any(math.hypot(x - px, y - py) <= near
                   for dx in (-1, 0, 1) for dy in (-1, 0, 1)
                   for x, y in grid.get((gx + dx, gy + dy), ()))
    return keep


def _sample_spots(rng: random.Random, reach: float, samples: int,
                  keep=None) -> list[tuple[float, float]]:
    """Random (east, north) offsets, uniform inside a disc of radius `reach`.
    If `keep` is given, spots it rejects (e.g. open water) are re-drawn."""
    spots: list[tuple[float, float]] = []
    attempts = 0
    while len(spots) < samples and attempts < samples * 50:
        attempts += 1
        r, theta = reach * math.sqrt(rng.random()), rng.random() * 2 * math.pi
        spot = (r * math.cos(theta), r * math.sin(theta))
        if keep is None or keep(*spot):
            spots.append(spot)
    return spots


def report_density(emit, scored: list[Scored], center: tuple[float, float], radius: int,
                   screen: tuple[int, int], zooms: list[int], samples: int, seed: int,
                   keep=None) -> None:
    emit(f"MARKERS PER SCREEN  ({screen[0]}x{screen[1]} px phone, {samples} random spots)")
    emit("  Counts BEFORE de-cluttering. Compare with your marker budget (12-15).")
    rng = random.Random(seed)
    lat0, lng0 = center
    offsets = [(s.tier, *_offset_m(s.place.lat, s.place.lng, lat0, lng0)) for s in scored]

    for zoom in zooms:
        m_per_px, half_w, half_h = _viewport(zoom, lat0, screen)
        reach = radius - math.hypot(half_w, half_h)  # keep the screen inside fetched data
        if reach <= 0:
            emit(f"  zoom {zoom}: skipped (screen is larger than the fetched area; raise --radius)")
            continue
        spots = _sample_spots(rng, reach, samples, keep)
        if not spots:
            emit(f"  zoom {zoom}: no land spots found to sample")
            continue
        emit(f"  zoom {zoom}: {m_per_px:.2f} m/px, screen ~ {2 * half_w:.0f} x {2 * half_h:.0f} m")
        for min_tier in (2, 3, 4):
            counts = sorted(
                sum(1 for tier, x, y in offsets
                    if tier >= min_tier and abs(x - px) <= half_w and abs(y - py) <= half_h)
                for px, py in spots
            )
            median = statistics.median(counts)
            p90 = counts[int(0.9 * (len(counts) - 1))]
            emit(f"      {stars(min_tier):<5}and up:  median {median:>5.0f}   p90 {p90:>4}   max {counts[-1]:>4}")
    emit()


def _view_counts(pool: list[tuple], spots: list[tuple[float, float]], half_w: float,
                 half_h: float, budget: int | None = None) -> list[int]:
    """How many pool items (points, tier, x, y) fall inside the screen at each spot.
    With a budget, only the highest-scoring `budget` items are kept (what the player sees)."""
    counts = []
    for px, py in spots:
        inside = [c for c in pool if abs(c[2] - px) <= half_w and abs(c[3] - py) <= half_h]
        if budget is not None:
            inside = sorted(inside, reverse=True)[:budget]
        counts.append(len(inside))
    return sorted(counts)


def _overworld_pool(shown: dict[str, Scored], cells: dict[str, Cell], zoom: int,
                    lat0: float, lng0: float) -> list[tuple]:
    """One icon per map tile at this zoom. Towns smaller than a tile merge into their parent
    tile (the quadtree gives us this for free); bigger towns keep their own icon."""
    groups: dict[Cell, list[Scored]] = defaultdict(list)
    for key, s in shown.items():
        z, x, y = cells[key]
        if z > zoom:
            shift = z - zoom
            z, x, y = zoom, x >> shift, y >> shift
        groups[(z, x, y)].append(s)
    pool = []
    for members in groups.values():
        pts = [_offset_m(m.place.lat, m.place.lng, lat0, lng0) for m in members]
        pool.append((max(m.points for m in members), max(m.tier for m in members),
                     sum(x for x, _ in pts) / len(pts), sum(y for _, y in pts) / len(pts)))
    return pool


def _pct(sorted_values: list[float], fraction: float) -> float:
    return sorted_values[int(fraction * (len(sorted_values) - 1))]


def _emit_sample_towns(emit, shown: dict[str, Scored], cells: dict[str, Cell], lat0: float) -> None:
    towns: dict[Cell, list[Scored]] = defaultdict(list)
    for key, s in shown.items():
        towns[cells[key]].append(s)
    ordered = sorted(towns.items(), key=lambda kv: -len(kv[1]))
    picks = ordered[:2] + ([ordered[len(ordered) // 2]] if len(ordered) > 4 else [])
    emit("    sample towns (the two busiest, plus a typical one):")
    for (zoom, _x, _y), members in picks:
        emit(f"      a town ~{cell_size_m(zoom, lat0):.0f} m wide, {len(members)} buildings:")
        for s in sorted(members, key=lambda s: -s.points):
            emit(f"        {stars(s.tier):<5} {themed_name(s.place.kind)}  {s.place.name}")


def report_towns(emit, scored: list[Scored], center: tuple[float, float], radius: int,
                 screen: tuple[int, int], zooms: list[int], samples: int, seed: int,
                 budget: int, limits: list[int], root_zoom: int, max_zoom: int,
                 sense_m: int, sample_limit: int, keep=None) -> None:
    items = [s for s in scored if slot_eligible(s)]
    lat0, lng0 = center
    emit(f"TOWN CELLS  ({len(items)} places can be town buildings)")
    emit("  Landmarks always show; everything else is one per category per town. The rest become")
    emit(f"  secrets (a '?' within {sense_m} m). 'raw' = markers before the {budget}-marker budget.")
    for limit in limits:
        cells = assign_cells(items, root_zoom, max_zoom, limit)
        shown = pick_shown(items, cells)
        leaves = set(cells.values())
        by_zoom = Counter(z for z, _, _ in leaves)
        sizes = ", ".join(f"{cell_size_m(z, lat0):.0f} m x{by_zoom[z]}" for z in sorted(by_zoom))
        landmarks = sum(1 for s in shown.values() if s.tier == 4)
        secrets = [s for s in items if s.place.key not in shown]
        emit(f"\n  split limit {limit}: {len(leaves)} towns ({sizes})")
        emit(f"    {len(shown)} buildings shown ({landmarks} landmarks), {len(secrets)} secrets")

        pool = [(s.points, s.tier, *_offset_m(s.place.lat, s.place.lng, lat0, lng0))
                for s in shown.values()]
        rng = random.Random(seed)
        for zoom in zooms:
            _, half_w, half_h = _viewport(zoom, lat0, screen)
            reach = radius - math.hypot(half_w, half_h)
            if reach <= 0:
                emit(f"    zoom {zoom}: skipped (screen is larger than the fetched area; raise --radius)")
                continue
            spots = _sample_spots(rng, reach, samples, keep)
            if not spots:
                emit(f"    zoom {zoom}: no land spots found to sample")
                continue
            icons = _view_counts(_overworld_pool(shown, cells, zoom, lat0, lng0), spots, half_w, half_h)
            raw = _view_counts(pool, spots, half_w, half_h)
            capped = _view_counts(pool, spots, half_w, half_h, budget)
            empty = 100 * sum(1 for n in capped if n == 0) / len(capped)
            emit(f"    zoom {zoom}: raw median {statistics.median(raw):>3.0f} p90 {_pct(raw, 0.9):>3} max {raw[-1]:>3}"
                 f" | with budget: median {statistics.median(capped):>3.0f} sparse {_pct(capped, 0.1):>3} empty {empty:>3.0f}%")
            emit(f"             or overworld icons (1 per tile): median {statistics.median(icons):>3.0f}"
                 f" p90 {_pct(icons, 0.9):>3} max {icons[-1]:>3}")

        secret_pts = [_offset_m(s.place.lat, s.place.lng, lat0, lng0) for s in secrets]
        near = sorted(
            sum(1 for x, y in secret_pts if math.hypot(x - px, y - py) <= sense_m)
            for px, py in _sample_spots(random.Random(seed), radius * 0.6, samples, keep)
        ) or [0]
        emit(f"    '?' within {sense_m} m of you: median {statistics.median(near):.0f}"
             f" | p90 {_pct(near, 0.9)} | max {near[-1]}")
        if limit == sample_limit:
            _emit_sample_towns(emit, shown, cells, lat0)
    emit()


def report_utility(emit, scored: list[Scored], center: tuple[float, float], radius: int,
                   samples: int, seed: int, keep=None) -> None:
    emit("SUPPLY POINTS (道具屋)  distance to the nearest konbini, supermarket or drinking fountain")
    lat0, lng0 = center
    kinds = Counter(s.place.kind for s in scored if s.place.kind in UTILITY_KINDS)
    supplies = [_offset_m(s.place.lat, s.place.lng, lat0, lng0)
                for s in scored if s.place.kind in UTILITY_KINDS]
    water = [_offset_m(s.place.lat, s.place.lng, lat0, lng0)
             for s in scored if s.place.kind == "drinking_water"]
    if not supplies:
        emit("  none found in this area (the hydration reminder needs a fallback here)")
        emit()
        return
    spots = _sample_spots(random.Random(seed), radius * 0.6, samples, keep)
    if not spots:
        emit("  no land spots found to sample")
        emit()
        return
    dists = sorted(min(math.hypot(x - px, y - py) for x, y in supplies) for px, py in spots)
    breakdown = ", ".join(f"{k} {n}" for k, n in kinds.most_common())
    emit(f"  {len(supplies)} supply points ({breakdown}); nearest from a random spot:"
         f" median {statistics.median(dists):.0f} m | p90 {_pct(dists, 0.9):.0f} m | max {dists[-1]:.0f} m")
    if water:
        wd = sorted(min(math.hypot(x - px, y - py) for x, y in water) for px, py in spots)
        emit(f"  drinking fountains only: median {statistics.median(wd):.0f} m"
             f" | p90 {_pct(wd, 0.9):.0f} m | max {wd[-1]:.0f} m")
    else:
        emit("  no drinking fountains mapped in this area")
    emit()


def report_app_coverage(emit, scored: list[Scored], top_kinds: int = 20) -> None:
    emit("COVERAGE OF THE APP'S CURRENT QUERY  (nodes only, unanchored regex)")
    emit("  How many places of each kind would the app's present Overpass query find?")
    totals = Counter(s.place.kind for s in scored if s.place.name)
    found = Counter(s.place.kind for s in scored if s.place.name and matches_current_app_query(s.place))
    emit(f"  {'kind':<20}{'exist':>7}{'found':>7}{'missed':>8}")
    for kind, n in totals.most_common(top_kinds):
        emit(f"  {kind:<20}{n:>7}{found[kind]:>7}{n - found[kind]:>8}")
    emit()


# =============================================================================
# MAIN
# =============================================================================

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Tune Unveil's place tiers against real OSM data.")
    p.add_argument("--lat", type=float, default=DEFAULT_CENTER[0])
    p.add_argument("--lng", type=float, default=DEFAULT_CENTER[1])
    p.add_argument("--radius", type=int, default=DEFAULT_RADIUS_M, help="fetch radius in metres")
    p.add_argument("--endpoint", default=OVERPASS_URL)
    p.add_argument("--cache", default="overpass_cache.json")
    p.add_argument("--refresh", action="store_true", help="ignore the cache and refetch")
    p.add_argument("--overrides", help='JSON file like {"node/123": 3} forcing a minimum tier')
    p.add_argument("--examples", type=int, default=15, help="examples per tier edge")
    p.add_argument("--zooms", type=int, nargs="+", default=[16, 17, 18])
    p.add_argument("--screen", default="390x780", help="phone viewport in px, WxH")
    p.add_argument("--samples", type=int, default=300, help="random spots for the density test")
    p.add_argument("--budget", type=int, default=15, help="max markers shown per screen")
    p.add_argument("--limits", type=int, nargs="+", default=TOWN_LIMITS,
                   help="town split limits to compare (a tile with more places splits in four)")
    p.add_argument("--root-zoom", type=int, default=ROOT_ZOOM, help="biggest town tile (15 = ~1 km)")
    p.add_argument("--max-zoom", type=int, default=MAX_ZOOM, help="smallest town tile (18 = ~125 m)")
    p.add_argument("--sense", type=int, default=SENSE_RADIUS_M, help="metres at which a '?' appears")
    p.add_argument("--land-near", type=int, default=0,
                   help="only sample spots within this many metres of any place (keeps sea and "
                        "mountains out of the stats; try 300 for Kobe). 0 = sample everywhere")
    p.add_argument("--seed", type=int, default=7)
    p.add_argument("--out", help="also write the report to this file")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    args = parse_args(argv)
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # stars + Japanese on any terminal
    except AttributeError:
        pass

    overrides = json.loads(Path(args.overrides).read_text(encoding="utf-8")) if args.overrides else None
    screen = tuple(int(v) for v in args.screen.lower().split("x"))

    places = dedupe(parse_elements(load_elements(args)))
    name_counts = Counter(p.name for p in places if p.name)
    scored = [score_place(p, overrides, name_counts) for p in places]

    lines: list[str] = []
    emit = lambda text="": lines.append(text)  # noqa: E731

    emit(f"Unveil tier analysis v{SCRIPT_VERSION} - {args.radius} m around {args.lat}, {args.lng}\n")
    report_summary(emit, scored)
    report_crosstab(emit, scored)
    report_signals(emit, scored)
    report_app_coverage(emit, scored)
    keep = _land_predicate(
        [_offset_m(s.place.lat, s.place.lng, args.lat, args.lng) for s in scored], args.land_near)
    report_density(emit, scored, (args.lat, args.lng), args.radius, screen,
                   args.zooms, args.samples, args.seed, keep)
    report_towns(emit, scored, (args.lat, args.lng), args.radius, screen, args.zooms,
                 args.samples, args.seed, args.budget, args.limits, args.root_zoom,
                 args.max_zoom, args.sense, args.limits[len(args.limits) // 2], keep)
    report_utility(emit, scored, (args.lat, args.lng), args.radius, args.samples, args.seed, keep)
    report_examples(emit, scored, args.examples)

    report = "\n".join(lines)
    print(report)
    if args.out:
        Path(args.out).write_text(report, encoding="utf-8")
        print(f"\n[report] saved to {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()