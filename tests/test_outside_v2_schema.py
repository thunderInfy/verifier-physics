"""Schema checks for the held-out outside benchmark v2 (benchmark/outside_v2)."""

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
V2 = ROOT / "benchmark" / "outside_v2"
V1_SOURCES = ROOT / "benchmark" / "outside" / "SOURCES.md"

FIELDS = {
    "id", "source_id", "location", "sentence", "scheme", "hypotheses",
    "expected_alone", "expected_with_hypotheses", "justification", "property",
}
VERDICTS = {"TRUE", "FALSE", "UNSURE"}
PROPERTIES = {
    "conservation", "order", "monotone", "tvd", "positivity", "entropy",
    "convergence", "stability", "shock_speed", "other",
}


def _rows(name):
    path = V2 / name
    assert path.exists(), path
    rows = []
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if line.strip():
            row = json.loads(line)
            assert isinstance(row, dict), (name, n)
            rows.append(row)
    return rows


def _v2_source_ids():
    text = (V2 / "SOURCES.md").read_text()
    sampled = text.split("## Dropped")[0]
    return set(re.findall(r"^\| `([a-z0-9_]+)` \|", sampled, flags=re.M))


def _v1_source_ids():
    return set(re.findall(r"`([a-z0-9_]+)`", V1_SOURCES.read_text()))


def _check(rows):
    for row in rows:
        assert set(row) == FIELDS, (row.get("id"), set(row) ^ FIELDS)
        for key in FIELDS - {"hypotheses"}:
            assert isinstance(row[key], str) and row[key].strip(), (row["id"], key)
        assert row["expected_alone"] in VERDICTS, row["id"]
        assert row["expected_with_hypotheses"] in VERDICTS, row["id"]
        assert row["property"] in PROPERTIES, row["id"]
        assert isinstance(row["hypotheses"], list), row["id"]
        for h in row["hypotheses"]:
            assert set(h) == {"hypothesis", "location"}, row["id"]
            assert all(isinstance(v, str) and v.strip() for v in h.values()), row["id"]
        assert re.fullmatch(rf"{re.escape(row['source_id'])}:\d\d", row["id"]), row["id"]


def test_items_schema():
    rows = _rows("items.jsonl")
    assert rows
    _check(rows)


def test_known_false_schema():
    _check(_rows("known_false.jsonl"))


def test_ids_unique():
    ids = [r["id"] for r in _rows("items.jsonl") + _rows("known_false.jsonl")]
    assert len(ids) == len(set(ids))


def test_per_source_cap():
    counts = {}
    for r in _rows("items.jsonl"):
        counts[r["source_id"]] = counts.get(r["source_id"], 0) + 1
    assert max(counts.values()) <= 15, counts


def test_items_come_from_listed_sources():
    listed = _v2_source_ids()
    assert listed
    for r in _rows("items.jsonl"):
        assert r["source_id"] in listed, r["id"]


def test_no_v1_source_reused():
    v1 = _v1_source_ids()
    assert v1
    used = {r["source_id"] for r in _rows("items.jsonl") + _rows("known_false.jsonl")}
    assert not (used | _v2_source_ids()) & v1


def test_skipped_log_parses():
    for r in _rows("skipped.jsonl"):
        assert {"source_id", "location", "sentence", "reason"} <= set(r)
        assert r["reason"].strip()
