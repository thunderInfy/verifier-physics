"""Schema checks for the v3 outside benchmark (benchmark/outside_v3)."""

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
V3 = ROOT / "benchmark" / "outside_v3"
EARLIER = [ROOT / "benchmark" / "outside" / "SOURCES.md", ROOT / "benchmark" / "outside_v2" / "SOURCES.md"]

FIELDS = {
    "id", "source_id", "location", "sentence", "scheme", "hypotheses", "quantifier", "quantifier_kind",
    "quantified_over", "expected_alone", "expected_with_hypotheses", "justification", "property",
}
TRUTH = {"TRUE", "FALSE", "UNSURE"}
KINDS = {"universal", "existential", "none"}
PROPERTIES = {
    "conservation", "consistency", "order", "monotone", "tvd", "positivity", "entropy", "convergence", "stability",
    "shock_speed", "other",
}


def _lines(name):
    return [json.loads(line) for line in (V3 / name).read_text().splitlines() if line.strip()]


def _sampled_sources():
    """(source_id, url) pairs from the 'Sampled sources' table of v3 SOURCES.md."""
    text = (V3 / "SOURCES.md").read_text()
    table = text.split("## Sampled sources", 1)[1].split("\n## ", 1)[0]
    rows = []
    for line in table.splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) >= 5 and cells[0].startswith("`"):
            urls = re.findall(r"https?://\S+", cells[4])
            rows.append((cells[0].strip("`"), urls))
    return rows


def _check_item(item):
    assert FIELDS <= item.keys(), FIELDS - item.keys()
    assert item["id"].startswith(item["source_id"] + ":")
    for key in ("location", "sentence", "scheme", "quantifier", "justification"):
        assert isinstance(item[key], str) and item[key].strip(), (item["id"], key)
    assert item["expected_alone"] in TRUTH
    assert item["expected_with_hypotheses"] in TRUTH
    assert item["quantifier_kind"] in KINDS
    assert item["property"] in PROPERTIES
    assert isinstance(item["quantified_over"], list)
    assert all(isinstance(q, str) for q in item["quantified_over"])
    assert isinstance(item["hypotheses"], list)
    for h in item["hypotheses"]:
        assert set(h) == {"text", "location", "standing"}, (item["id"], h)
        assert isinstance(h["text"], str) and h["text"].strip()
        assert h["location"] is None or isinstance(h["location"], str)
        assert isinstance(h["standing"], bool)


def test_items_and_known_false_schema():
    items = _lines("items.jsonl")
    known_false = _lines("known_false.jsonl")
    assert items
    for item in items + known_false:
        _check_item(item)
    ids = [i["id"] for i in items + known_false]
    assert len(ids) == len(set(ids))


def test_items_come_from_listed_sources_within_cap():
    sources = {sid for sid, _ in _sampled_sources()}
    counts = {}
    for item in _lines("items.jsonl"):
        assert item["source_id"] in sources, item["source_id"]
        counts[item["source_id"]] = counts.get(item["source_id"], 0) + 1
    assert max(counts.values()) <= 15


def test_skipped_log_parses():
    for entry in _lines("skipped.jsonl"):
        assert {"source_id", "location", "sentence", "reason"} <= entry.keys()
        assert entry["reason"].strip()


def test_no_overlap_with_earlier_benchmarks():
    earlier = "\n".join(p.read_text() for p in EARLIER)
    rows = _sampled_sources()
    assert rows
    for sid, urls in rows:
        assert sid not in earlier, sid
        assert urls, sid
        for url in urls:
            assert url not in earlier, url
    for item in _lines("items.jsonl") + _lines("known_false.jsonl"):
        assert item["source_id"] not in earlier
