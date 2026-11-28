"""Outside benchmark v2, phase A0: the blind readers' view, the agreement subset, the frozen items and the
standing-condition audit."""

import hashlib
import importlib.util
import json
from pathlib import Path

D = Path(__file__).resolve().parent.parent / "benchmark" / "outside_v2"
ALLOWED = {"id", "sentence", "scheme", "hypotheses", "location"}
# sha256 of items.jsonl as frozen in commit 63337e1 (git show 63337e1:benchmark/outside_v2/items.jsonl).
FROZEN_SHA256 = "df9b49aaff107752a728313039f165dfb1338c77da70e082b55d2314cd1b7f05"


def load_strip():
    spec = importlib.util.spec_from_file_location("strip_v2", D / "strip_v2.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def jsonl(name):
    return [json.loads(line) for line in (D / name).read_text().splitlines()]


def item_ids():
    return [o["id"] for o in jsonl("items.jsonl")]


def test_items_byte_identical_to_freeze():
    assert hashlib.sha256((D / "items.jsonl").read_bytes()).hexdigest() == FROZEN_SHA256


def test_stripped_has_only_allowed_keys_and_95_lines():
    rows = jsonl("stripped.jsonl")
    assert len(rows) == 95
    for r in rows:
        assert set(r) == ALLOWED, r["id"]
    assert [r["id"] for r in rows] == item_ids()


def test_stripped_is_current_output_of_script():
    assert jsonl("stripped.jsonl") == load_strip().stripped_rows()


def test_subset_matches_sha256_mod_4_rule():
    want = [i for i in item_ids() if int(hashlib.sha256(i.encode("utf-8")).hexdigest(), 16) % 4 == 0]
    got = (D / "subset_a2.txt").read_text().splitlines()
    assert got == want
    assert got


def test_standing_conditions_refer_to_existing_items():
    ids = set(item_ids())
    rows = jsonl("standing_conditions.jsonl")
    assert rows
    for r in rows:
        assert r["id"] in ids, r["id"]
        assert r["condition"]
        assert isinstance(r["derived"], bool)
        # Derived means printed nowhere: then there is no quote and no allowed location.
        if r["derived"]:
            assert r["printed_at"] is None and r["quote"] is None and r["location"] is None, r["id"]
        else:
            assert r["printed_at"] and r["quote"], r["id"]


def test_null_location_items_are_in_errata():
    errata = (D / "ERRATA.md").read_text()
    section = errata.split("## Post-freeze: standing-condition rule (2026-11-28)", 1)[1]
    for i in {r["id"] for r in jsonl("standing_conditions.jsonl") if r["location"] is None}:
        assert f"| `{i}` | expected_alone |" in section, i
