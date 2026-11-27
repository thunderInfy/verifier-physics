"""Schema checks for the outside benchmark in benchmark/outside/ (data only, no checker is run)."""

import hashlib
import json
import re
from pathlib import Path

D = Path(__file__).resolve().parent.parent / "benchmark" / "outside"

FIELDS = ["id", "source_id", "location", "sentence", "scheme", "hypotheses",
          "expected_alone", "expected_with_hypotheses", "justification", "property"]
VERDICTS = {"TRUE", "FALSE", "UNSURE"}
PROPERTIES = {"conservation", "order", "monotone", "tvd", "positivity", "entropy",
              "convergence", "stability", "shock_speed", "other"}


def load(name):
    rows = []
    for n, line in enumerate((D / name).read_text().splitlines(), 1):
        if line.strip():
            rows.append((n, json.loads(line)))
    return rows


def sources_listed():
    return set(re.findall(r"^\| `([a-z0-9_]+)` \|", (D / "SOURCES.md").read_text(), re.M))


def check_item(name, n, o):
    where = f"{name}:{n}"
    for f in FIELDS:
        assert f in o, f"{where}: missing {f}"
    for f in ["id", "source_id", "location", "sentence", "justification"]:
        assert isinstance(o[f], str) and o[f].strip(), f"{where}: {f} must be a non-empty string"
    assert o["expected_alone"] in VERDICTS, where
    assert o["expected_with_hypotheses"] in VERDICTS, where
    assert o["property"] in PROPERTIES, where
    s = o["scheme"]
    assert isinstance(s, dict) and s.get("definition", "").strip() and s.get("location", "").strip(), where
    assert isinstance(o["hypotheses"], list), where
    for h in o["hypotheses"]:
        assert isinstance(h, dict) and h.get("hypothesis", "").strip() and h.get("location", "").strip(), where
    assert o.get("text_note", "ocr_normalized") == "ocr_normalized", where


def test_items_schema():
    rows = load("items.jsonl")
    assert rows
    listed = sources_listed()
    ids = [o["id"] for _, o in rows]
    assert len(ids) == len(set(ids)), "duplicate item ids"
    for n, o in rows:
        check_item("items.jsonl", n, o)
        assert o["source_id"] in listed, f"items.jsonl:{n}: source not in SOURCES.md"


def test_known_false_schema():
    rows = load("known_false.jsonl")
    assert rows
    ids = [o["id"] for _, o in rows]
    assert len(ids) == len(set(ids))
    for n, o in rows:
        check_item("known_false.jsonl", n, o)
        r = o.get("refutation")
        assert isinstance(r, dict), f"known_false.jsonl:{n}: missing refutation"
        for f in ["source", "url", "location", "quote"]:
            assert r.get(f, "").strip(), f"known_false.jsonl:{n}: refutation.{f}"
    item_ids = {o["id"] for _, o in load("items.jsonl")}
    assert not item_ids & set(ids), "known-false ids must not appear in items.jsonl"


def test_skipped_parses():
    for n, o in load("skipped.jsonl"):
        for f in ["source_id", "location", "sentence", "reason"]:
            assert isinstance(o.get(f), str) and o[f].strip(), f"skipped.jsonl:{n}: {f}"


def half(source_id):
    return "dev" if int(hashlib.sha256(source_id.encode()).hexdigest(), 16) % 2 == 0 else "heldout"


def test_frozen_split_matches_hash_rule():
    text = (D / "FROZEN.md").read_text()
    rows = re.findall(r"^\| `([a-z0-9_]+)` \| (dev|heldout) \| (\d+) \|", text, re.M)
    assert rows, "no split table in FROZEN.md"
    split = {sid: h for sid, h, _ in rows}
    for sid, h in split.items():
        assert h == half(sid), f"{sid}: FROZEN.md says {h}, hash rule says {half(sid)}"
    counts = {}
    for _, o in load("items.jsonl"):
        counts[o["source_id"]] = counts.get(o["source_id"], 0) + 1
    assert set(counts) <= set(split), "items from a source missing in FROZEN.md"
    for sid, _, c in rows:
        assert counts.get(sid, 0) == int(c), f"{sid}: FROZEN.md count {c}, items.jsonl {counts.get(sid, 0)}"
    assert "Expected values are frozen as of this commit; any correction goes to ERRATA.md with before/after." in text
    assert (D / "ERRATA.md").exists()
