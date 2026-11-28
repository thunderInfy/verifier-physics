"""The dev half of the outside benchmark: formal readings (benchmark/outside/dev_readings.json), their
verdicts and scores against the frozen expected values. Recomputes every verdict (about 5 s)."""
import importlib.util
import json
from pathlib import Path

import pytest

from physverify.schemes import claims as C

B = Path(__file__).resolve().parent.parent / "benchmark" / "outside"
_spec = importlib.util.spec_from_file_location("run_dev", B / "run_dev.py")
run_dev = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(run_dev)


@pytest.fixture(scope="module")
def rows(checked):
    data, items = run_dev.load(), run_dev.dev_items()
    return run_dev.evaluate(data, items, run_dev.run(data, checker=checked))


def test_readings_cover_exactly_the_dev_items():
    data, items = run_dev.load(), run_dev.dev_items()
    assert len(items) == 99
    assert not run_dev.validate(data, items)
    heldout = [json.loads(line)["id"] for line in (B / "items.jsonl").read_text().splitlines()
               if run_dev.half(json.loads(line)["source_id"]) == "heldout"]
    text = (B / "dev_readings.json").read_text()
    assert len(heldout) == 77 and not [i for i in heldout if f'"{i}"' in text]


def test_negation_flips_only_what_it_may():
    flip = lambda v: run_dev.NEGATE.get(v, v)
    assert [flip(v) for v in (C.VERIFIED, C.REFUTED, C.REFUTED_EMPIRICALLY, C.NOT_REFUTED, C.UNKNOWN)] == \
        [C.REFUTED, C.VERIFIED, C.NOT_REFUTED, C.UNKNOWN, C.UNKNOWN]
    assert [run_dev.score("TRUE", v) for v in (C.VERIFIED, C.REFUTED, C.NOT_REFUTED, C.INCONSISTENT)] == \
        ["MATCH", "WRONG", "GAP", "BUG"]
    assert [run_dev.score("FALSE", C.REFUTED_EMPIRICALLY), run_dev.score("UNSURE", C.VERIFIED)] == ["MATCH", "UNSCORED"]


def test_stored_verdicts_and_scores_are_what_the_checker_gives_now(rows):
    for r in rows:
        e = r["_e"]
        assert [rd["actual"] for rd in e["readings"]] == r["actual"], r["id"]
        assert e["score"] == r["score"], r["id"]


def test_no_wrong_verdict_and_every_gap_reading_is_explained(rows):
    assert not run_dev.summary(rows)["wrong"]
    undecided = [(r["id"], rd["reading"][:40]) for r in rows for rd, a in zip(r["_e"]["readings"], r["actual"])
                 if a["verdict"] not in run_dev.DECIDED]
    assert undecided == [(r["id"], rd["reading"][:40]) for r in rows for rd in r["_e"]["readings"] if rd.get("gap")]


def test_headline_numbers_in_dev_results(rows):
    s = run_dev.summary(rows)
    assert (s["stated"], s["readings"], s["decided"]) == (22, 27, 26)
    assert (s["tuned_readings"], s["tuned_matches"]) == (9, 14)
    text = (B / "DEV_RESULTS.md").read_text()
    for needle in (f"{s['stated']} of {s['items']}", f"{s['decided']} of {s['readings']}"):
        assert needle in text


def test_narrowing_rule_maps_a_narrowed_reading_to_the_sentence():
    # 'for every slope' (FALSE), narrowed to one slope where the checker verifies it: WRONG as frozen,
    # not decided (GAP) under the opt-in rule, with the instance's verdict kept
    c = {"spec": "s.json", "claim": "tvd"}
    r = {"field": "both", "formalization": [c], "narrowing": "one slope",
         "narrowed": [{"param": "slope", "quantifier": "universal"}]}
    data = {"items": [{"id": "x", "readings": [r], "unformalized": []}]}
    items = {"x": {"property": "p", "expected_alone": "FALSE", "expected_with_hypotheses": "FALSE"}}
    verdicts = {run_dev._key(c): {"tvd": C.VERIFIED}}
    frozen, = run_dev.evaluate(data, items, verdicts)
    ruled, = run_dev.evaluate(data, items, verdicts, narrowing_rule=True)
    assert frozen["score"] == {"alone": "WRONG", "with_hypotheses": "WRONG"} and "instance_verdict" not in frozen["actual"][0]
    assert ruled["score"] == {"alone": "GAP", "with_hypotheses": "GAP"}
    assert (ruled["actual"][0]["instance_verdict"], ruled["actual"][0]["verdict"]) == (C.VERIFIED, C.NOT_REFUTED)


def test_dev_and_heldout_share_one_deep_merge(rows):
    """run_heldout.py uses run_dev.deep_merge, so dev and heldout apply overrides the same way, and the switch of
    run_dev from bench._spec's one-level merge to it moved no dev score (the scores recomputed with it equal
    those stored in dev_readings.json, which were written before the switch)."""
    _h = importlib.util.spec_from_file_location("run_heldout_for_dev", B / "run_heldout.py")
    run_heldout = importlib.util.module_from_spec(_h)
    _h.loader.exec_module(run_heldout)
    where = lambda f: (Path(f.__code__.co_filename).name, f.__code__.co_firstlineno)
    assert where(run_heldout.deep_merge) == where(run_dev.deep_merge) == ("run_dev.py", run_dev.deep_merge.__code__.co_firstlineno)
    assert run_dev.deep_merge({"a": {"b": 1, "c": 2}, "l": [1]}, {"a": {"b": 3}, "l": [2]}) == \
        {"a": {"b": 3, "c": 2}, "l": [2]}
    stored = {e["id"]: e["score"] for e in json.loads((B / "dev_readings.json").read_text())["items"]}
    assert {r["id"]: r["score"] for r in rows} == stored
