"""Tests for the pure logic in tier_analysis.py.  Run with:  python3 -m pytest -q"""

import math
import random

from tier_analysis import (
    THEMED_NAMES, UTILITY_KINDS, _land_predicate, _overworld_pool, _sample_spots, Place, assign_cells, classify, dedupe, matches_current_app_query,
    parse_elements, pick_shown, score_place, slot_eligible, tile_of,
)


def make(kind="cafe", name="テスト", key="node/1", tags=None, area=None, lat=34.69, lng=135.19):
    return Place(key=key, lat=lat, lng=lng, name=name, kind=kind, tags=tags or {}, area_m2=area)


# ---- classify ----------------------------------------------------------------

def test_shinto_worship_is_a_shrine():
    assert classify({"amenity": "place_of_worship", "religion": "shinto"}) == "shrine"


def test_buddhist_worship_is_a_temple():
    assert classify({"amenity": "place_of_worship", "religion": "buddhist"}) == "temple"


def test_christian_worship_is_a_church():
    assert classify({"amenity": "place_of_worship", "religion": "christian"}) == "church"


def test_untagged_worship_stays_generic():
    assert classify({"amenity": "place_of_worship"}) == "place_of_worship"
    assert THEMED_NAMES["place_of_worship"] == "小さな祠"


def test_ryokan_and_guest_houses_are_inns_but_business_hotels_are_not():
    assert classify({"tourism": "guest_house", "name": "民宿 かもめ"}) == "inn"
    assert classify({"tourism": "hotel", "name": "有馬の旅館 山水"}) == "inn"
    assert classify({"tourism": "hotel", "name": "神戸ベイホテル"}) == "hotel"
    assert classify({"tourism": "hostel", "name": "旅館風ホステル"}) == "hotel"
    assert THEMED_NAMES["inn"] == THEMED_NAMES["hotel"] == "宿屋"


def test_tourism_beats_amenity():
    assert classify({"tourism": "museum", "amenity": "cafe"}) == "museum"


# ---- scoring -----------------------------------------------------------------

def test_unnamed_places_are_hidden():
    assert score_place(make(name=None, kind="shrine", tags={"wikidata": "Q1"})).tier == 1


def test_plain_independent_cafe_is_local():
    assert score_place(make("cafe")).tier == 2


def test_chain_convenience_store_is_hidden():
    assert score_place(make("convenience", "ローソン")).tier == 1
    assert score_place(make("convenience", "Corner Shop", tags={"brand": "X"})).tier == 1


def test_wikidata_alone_is_notable_but_wikipedia_makes_a_landmark():
    assert score_place(make("shrine", tags={"wikidata": "Q1"})).tier == 3
    assert score_place(make("shrine", tags={"wikidata": "Q1", "wikipedia": "ja:x"})).tier == 4


def test_plain_restaurant_is_hidden_but_a_documented_one_shows():
    assert score_place(make("restaurant")).tier == 1
    assert score_place(make("restaurant", tags={"opening_hours": "10:00-20:00"})).tier == 1
    assert score_place(make("restaurant", tags={"name:en": "Kobe Beef"})).tier == 2


def test_local_fast_food_gem_is_visible_but_chain_is_not():
    gem = make("fast_food", "老祥記", tags={"name:en": "Rosyoki", "opening_hours": "x"})
    assert score_place(gem).tier == 2
    assert score_place(make("fast_food", "マクドナルド", tags={"name:en": "McD"})).tier == 1


def test_branch_style_names_are_penalised_for_businesses_only():
    assert score_place(make("restaurant", "麺屋 天孫降臨 元町店", tags={"name:en": "x"})).tier == 1
    assert score_place(make("restaurant", "餃子屋 満園 三宮店（2号店）", tags={"name:en": "x"})).tier == 1
    # a shrine with a similar-looking name is not a chain
    assert score_place(make("shrine", "なんとか 本店")).tier == 2


def test_repeated_names_flag_businesses_not_shrines():
    from collections import Counter
    counts = Counter({"みどり": 5, "稲荷神社": 5})
    assert score_place(make("cafe", "みどり", tags={"name:en": "x"}), name_counts=counts).tier == 1
    assert score_place(make("shrine", "稲荷神社"), name_counts=counts).tier == 2


def test_minor_memorials_are_hidden():
    assert classify({"historic": "memorial", "memorial": "plaque"}) == "memorial_minor"
    assert score_place(make("memorial_minor", "顕彰状")).tier == 1
    assert score_place(make("memorial", "震災メモリアル")).tier == 1  # plain memorial needs a signal


def test_plain_neighbourhood_shrine_is_local():
    assert score_place(make("shrine")).tier == 2


def test_documented_shrine_is_notable():
    tags = {"name:en": "Ikuta", "website": "https://example.org"}
    assert score_place(make("shrine", tags=tags)).tier == 3


def test_untagged_museum_is_local_but_documented_museum_is_notable():
    assert score_place(make("museum")).tier == 2
    assert score_place(make("museum", tags={"name:en": "Museum"})).tier == 3


def test_big_park_gets_area_bonus():
    small = score_place(make("park", area=5_000))
    big = score_place(make("park", area=120_000))
    assert big.points == small.points + 15


def test_override_only_raises_never_lowers():
    s = make("cafe", key="node/9")
    assert score_place(s, {"node/9": 3}).tier == 3
    assert score_place(make("castle", key="node/9", tags={"wikidata": "Q1"}), {"node/9": 2}).tier == 4


# ---- parsing + de-duplication --------------------------------------------------

def test_way_gets_centre_and_area_from_bounds():
    el = {"type": "way", "id": 5, "tags": {"leisure": "park", "name": "公園"},
          "bounds": {"minlat": 34.690, "maxlat": 34.692, "minlon": 135.190, "maxlon": 135.193}}
    (place,) = parse_elements([el])
    assert place.kind == "park" and place.area_m2 and place.area_m2 > 10_000


def test_elements_without_location_are_skipped():
    assert parse_elements([{"type": "relation", "id": 1, "tags": {"name": "x"}}]) == []


def test_duplicate_node_and_building_collapse_to_one():
    a = make("shrine", "生田神社", key="node/1", tags={"wikidata": "Q1", "religion": "shinto"})
    b = make("shrine", "生田神社", key="way/2", tags={}, lat=34.69001)
    assert len(dedupe([a, b])) == 1


def test_same_name_far_apart_is_kept():
    a = make("cafe", "珈琲店", key="node/1")
    b = make("cafe", "珈琲店", key="node/2", lat=34.70)
    assert len(dedupe([a, b])) == 2


# ---- the app's current query -----------------------------------------------------

def test_current_app_query_misses_ways_and_worship_sites():
    shrine = make("shrine", key="node/1", tags={"amenity": "place_of_worship", "religion": "shinto"})
    park_way = make("park", key="way/2", tags={"leisure": "park"})
    cafe = make("cafe", key="node/3", tags={"amenity": "cafe"})
    assert not matches_current_app_query(shrine)
    assert not matches_current_app_query(park_way)
    assert matches_current_app_query(cafe)


# ---- the JRPG town system ------------------------------------------------------------

def scored(kind, name, key, tags=None, lat=34.69, lng=135.19):
    return score_place(make(kind, name, key=key, tags=tags or {}, lat=lat, lng=lng))


def test_cafes_and_bars_get_separate_slots():
    assert THEMED_NAMES["cafe"] == "茶屋"
    assert THEMED_NAMES["cafe"] != THEMED_NAMES["bar"]
    assert THEMED_NAMES["bar"] == THEMED_NAMES["pub"] == "酒場"  # these two still compete


def test_konbini_chains_and_unnamed_places_are_not_town_buildings():
    assert not slot_eligible(scored("convenience", "コンビニ", "node/1", {"name:en": "x"}))
    assert not slot_eligible(scored("cafe", "スターバックス", "node/2"))
    assert not slot_eligible(scored("shrine", None, "node/3"))
    assert not slot_eligible(scored("other", "謎", "node/4"))
    assert slot_eligible(scored("cafe", "珈琲店", "node/5"))


def test_tile_of_known_values():
    assert tile_of(0.0, 0.0, 1) == (1, 1)
    assert tile_of(35.0, 135.0, 0) == (0, 0)
    # one zoom level down quarters the tile: the parent's x is the child's x // 2
    cx, cy = tile_of(34.69, 135.19, 16)
    assert tile_of(34.69, 135.19, 15) == (cx // 2, cy // 2)


def test_dense_tiles_split_and_sparse_ones_do_not():
    cluster = [scored("cafe", f"店{i}", f"node/{i}", lat=34.690, lng=135.190) for i in range(5)]
    loner = scored("cafe", "ひとり", "node/99", lat=34.760, lng=135.190)
    cells = assign_cells(cluster + [loner], root_zoom=10, max_zoom=18, limit=3)
    assert all(cells[s.place.key][0] == 18 for s in cluster)  # identical spots can never separate
    assert cells["node/99"][0] < 18  # a lone place stops splitting as soon as it is alone


def test_one_winner_per_slot_and_landmarks_always_show():
    cell = (17, 1, 1)
    a = scored("shrine", "小社A", "node/1")
    b = scored("shrine", "小社B", "node/2", {"name:en": "B"})           # better documented
    c = scored("shrine", "大社C", "node/3", {"wikidata": "Q1", "wikipedia": "ja:C"})  # landmark
    d = scored("shrine", "大社D", "node/4", {"wikidata": "Q2", "wikipedia": "ja:D"})  # landmark
    items = [a, b, c, d]
    shown = pick_shown(items, {s.place.key: cell for s in items})
    assert set(shown) == {"node/3", "node/4"}  # C wins the slot, D bypasses it as a landmark

    only_two = pick_shown([a, b], {s.place.key: cell for s in (a, b)})
    assert set(only_two) == {"node/2"}  # the better-documented one wins; A becomes a secret


def test_different_categories_in_one_town_all_show():
    cell = (17, 1, 1)
    items = [scored("cafe", "茶房", "node/1"), scored("bar", "夜の店", "node/2"),
             scored("restaurant", "食堂", "node/3"), scored("shrine", "社", "node/4")]
    assert len(pick_shown(items, {s.place.key: cell for s in items})) == 4


def test_the_same_category_in_different_towns_both_show():
    a, b = scored("cafe", "東の茶屋", "node/1"), scored("cafe", "西の茶屋", "node/2")
    shown = pick_shown([a, b], {"node/1": (17, 1, 1), "node/2": (17, 2, 1)})
    assert len(shown) == 2


# ---- sampling with a land mask -------------------------------------------------------

def test_land_mask_rejects_open_water_but_keeps_spots_near_places():
    keep = _land_predicate([(0.0, 0.0)], near=300)
    assert keep(100, 100) is True
    assert keep(1000, 0) is False
    assert _land_predicate([(0.0, 0.0)], near=0) is None  # 0 means "sample everywhere"


def test_sampling_only_returns_spots_the_mask_accepts():
    keep = _land_predicate([(0.0, 0.0)], near=300)
    spots = _sample_spots(random.Random(1), reach=600, samples=50, keep=keep)
    assert len(spots) == 50
    assert all(math.hypot(x, y) <= 300 for x, y in spots)


def test_untagged_archaeological_site_is_only_local():
    assert score_place(make("archaeological_site", "防火水そう")).tier == 2
    assert score_place(make("archaeological_site", "遺跡", tags={"wikidata": "Q1"})).tier == 3


# ---- suburban categories ----------------------------------------------------------------

def test_new_kinds_classify():
    assert classify({"railway": "station"}) == "station"
    assert classify({"railway": "halt"}) == "station"
    assert classify({"amenity": "post_office"}) == "post_office"
    assert classify({"amenity": "townhall"}) == "townhall"
    assert classify({"amenity": "pharmacy"}) == "pharmacy"
    assert classify({"natural": "peak"}) == "peak"
    assert classify({"natural": "spring"}) == "spring"
    assert classify({"waterway": "waterfall"}) == "waterfall"
    assert classify({"amenity": "drinking_water"}) == "drinking_water"


def test_new_kinds_have_in_world_names():
    kinds = ("post_office", "station", "townhall", "pharmacy", "peak", "spring", "waterfall")
    assert [THEMED_NAMES[k] for k in kinds] == ["飛脚屋", "宿場", "役所", "薬屋", "霊峰", "名水", "滝"]


def test_civic_buildings_are_not_treated_as_chains_but_cafes_still_are():
    post = scored("post_office", "神戸谷上郵便局", "node/1", {"brand": "日本郵便"})
    assert not post.chain and slot_eligible(post)
    assert scored("cafe", "どこかのカフェ", "node/2", {"brand": "X"}).chain


def test_drinking_fountains_are_supply_points_not_town_buildings():
    fountain = scored("drinking_water", "水飲み場", "node/3")
    assert "drinking_water" in UTILITY_KINDS
    assert not slot_eligible(fountain)


def test_overworld_icons_merge_small_towns_into_the_tile_at_that_zoom():
    lat, lng = 34.6901, 135.1956
    a = scored("cafe", "東", "node/1", lat=lat, lng=lng)
    b = scored("shrine", "西", "node/2", lat=lat + 0.003, lng=lng)  # ~330 m away
    shown = {s.place.key: s for s in (a, b)}
    cells = {s.place.key: (18, *tile_of(s.place.lat, s.place.lng, 18)) for s in (a, b)}
    assert len(_overworld_pool(shown, cells, 18, lat, lng)) == 2   # two separate 125 m towns
    assert len(_overworld_pool(shown, cells, 10, lat, lng)) == 1   # one icon at a very far zoom
