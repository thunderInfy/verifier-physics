"""The heldout half of the outside benchmark, phase B (benchmark/outside/run_heldout.py): the pin, the override
merge, and that HELDOUT_RESULTS.md and heldout_verdicts.json are what the frozen checker gives now."""
import copy
import importlib.util
import json
from pathlib import Path

import pytest

from physverify import reconstruction

B = Path(__file__).resolve().parent.parent / "benchmark" / "outside"
_spec = importlib.util.spec_from_file_location("run_heldout", B / "run_heldout.py")
H = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(H)


def test_checker_and_readings_are_frozen():
    assert H.frozen_errors() == []
    assert H.PIN in (B / "HELDOUT_PIN.md").read_text()
    for c in H.READINGS_COMMITS.values():
        assert c in (B / "HELDOUT_PIN.md").read_text()


def test_deep_merge_keeps_what_the_override_does_not_name():
    assert H.deep_merge({"a": {"b": 1, "c": [1]}, "d": 2}, {"a": {"c": [2], "e": 3}}) == \
        {"a": {"b": 1, "c": [2], "e": 3}, "d": 2}


def test_weno_m_override_gives_the_hand_edited_spec_and_a_different_reconstruction():
    c = H.WENO_M
    base = json.loads((H.SPECS / c["spec"]).read_text())
    hand = copy.deepcopy(base)
    hand["reconstruction"]["weights"]["kind"] = "m"
    merged = H.merged_spec(c)
    assert merged == hand and merged != base
    assert merged["reconstruction"]["weights"]["d"] == base["reconstruction"]["weights"]["d"]
    # not just the key: the checker builds a different reconstruction and decides the claim differently
    assert reconstruction.parse_reconstruction(merged["reconstruction"])["kind"] == "m"
    claim = {"claim": c["claim"], **c["params"]}
    assert reconstruction.check_claim(merged["reconstruction"], claim)["verdict"] == "VERIFIED"
    assert reconstruction.check_claim(base["reconstruction"], claim)["verdict"] == "REFUTED"
    assert H.override_demo() == {"component": c, "merged": "VERIFIED", "base": "REFUTED"}


@pytest.fixture(scope="module")
def fresh():
    return H.compute()


def test_stored_verdicts_are_what_the_checker_gives_now(fresh):
    assert json.loads((B / "heldout_verdicts.json").read_text()) == json.loads(json.dumps(fresh, ensure_ascii=False))


def test_results_md_is_generated_from_the_verdicts_json():
    stored = json.loads((B / "heldout_verdicts.json").read_text())
    assert (B / "HELDOUT_RESULTS.md").read_text() == H.render(stored)


def test_every_wrong_is_classed_and_contaminated_sources_are_split_out(fresh):
    for r in fresh["rows"]:
        for f, c in r.get("wrong_class", {}).items():
            assert c["class"] in ("checker", "reading") and c["why"], (r["id"], f)
    t = fresh["headline"]
    assert t["all"]["items"] == 77
    assert t["without both contaminated sources"]["items"] == 77 - len(fresh["contaminated_items"])


def test_erratum_candidate_rests_on_an_exact_check(fresh):
    e = fresh["erratum_candidate"]
    assert e["as_printed"]["check_status"] == "REFUTED" and e["as_printed"]["guarantee"].startswith("exact")
    assert e["with_dv_factor"]["check_status"] == "VERIFIED"
    assert all(s["A2_score"] == "ERRATUM_CANDIDATE" for s in fresh["a2_sensitivity"] if s["id"] == e["id"])
    assert "tadmor_2003_acta:17" in (B / "ERRATA_PROPOSED.md").read_text()
