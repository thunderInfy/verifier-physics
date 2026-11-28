"""The blind readers' view of the heldout split: allowed keys only, 77 items, subset by the sha256 % 4 rule."""

import hashlib
import importlib.util
import json
from pathlib import Path

D = Path(__file__).resolve().parent.parent / "benchmark" / "outside"
ALLOWED = {"item_id", "sentence", "scheme", "hypotheses", "location"}


def load_strip():
    spec = importlib.util.spec_from_file_location("strip_heldout", D / "strip_heldout.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def stripped():
    return [json.loads(line) for line in (D / "heldout_stripped.jsonl").read_text().splitlines()]


def test_stripped_has_only_allowed_keys_and_77_lines():
    rows = stripped()
    assert len(rows) == 77
    for r in rows:
        assert set(r) == ALLOWED, r["item_id"]
    assert len({r["item_id"] for r in rows}) == 77


def test_stripped_is_current_output_of_script():
    # The committed file is exactly what the script writes from items.jsonl.
    assert stripped() == load_strip().stripped_rows()


def test_subset_matches_sha256_mod_4_rule():
    ids = [r["item_id"] for r in stripped()]
    want = [i for i in ids if int(hashlib.sha256(i.encode("utf-8")).hexdigest(), 16) % 4 == 0]
    got = (D / "heldout_subset_a2.txt").read_text().splitlines()
    assert got == want
    assert got
