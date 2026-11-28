"""The narrowing polarity rule (physverify/schemes/narrowing.py) and its post-hoc effect on bench v2
(benchmark/outside_v2/posthoc.py, POSTHOC_NARROWING.md). The rule is opt-in: the frozen runs do not set it."""
import importlib.util
from pathlib import Path

import pytest

from physverify.claimkinds import KINDS
from physverify.schemes import narrowing as N

U, E = N.UNIVERSAL, N.EXISTENTIAL
SLOPE_U = [{"param": "slope", "quantifier": U}]
CFL_E = [{"param": "cfl", "quantifier": E}]


def test_universal_false_sentence_narrowed_to_a_true_instance_is_not_decided():
    # 'stable for every slope' (FALSE), narrowed to the central slope, where it holds
    assert N.sentence_verdict("VERIFIED", "central slope", SLOPE_U) == "NOT_REFUTED"


def test_universal_sentence_narrowed_to_a_failing_instance_is_refuted():
    assert N.sentence_verdict("REFUTED", "one slope", SLOPE_U) == "REFUTED"
    assert N.sentence_verdict("REFUTED_EMPIRICALLY", "one slope", SLOPE_U) == "REFUTED_EMPIRICALLY"


def test_existential_instance_verified_verifies_and_refuted_says_nothing():
    assert N.sentence_verdict("VERIFIED", "nu in (0, 1/4]", CFL_E) == "VERIFIED"
    assert N.sentence_verdict("REFUTED", "nu in (0, 1/4]", CFL_E) == "UNKNOWN"
    assert N.sentence_verdict("NOT_REFUTED", "nu in (0, 1/4]", CFL_E) == "NOT_REFUTED"   # empirical never verifies


def test_unrecorded_or_mixed_quantifier_is_unknown():
    assert N.sentence_verdict("VERIFIED", "f = u", None) == "UNKNOWN"
    assert N.sentence_verdict("REFUTED", "f = u", [{"param": "flux"}]) == "UNKNOWN"
    assert N.sentence_verdict("REFUTED", "two", SLOPE_U + CFL_E) == "UNKNOWN"


def test_not_narrowed_is_unchanged():
    for v in ("VERIFIED", "REFUTED", "UNKNOWN", "SPEC_ERROR", "INCONSISTENT"):
        assert N.sentence_verdict(v, None, None) == v
        assert N.sentence_verdict(v, "", SLOPE_U) == v


def test_negation_swaps_the_quantifier():
    # reading 'not (for every slope ...)' verified on one slope: an existential witness
    assert N.sentence_verdict("VERIFIED", "one slope", SLOPE_U, negated=True) == "VERIFIED"


def test_cfl_quantifier_from_the_registry():
    assert N.cfl_quantifier("stable_for_small_cfl") == E
    assert N.cfl_quantifier("von_neumann_stable_under_cfl") == U
    assert N.cfl_quantifier("positive_under_cfl") == U
    assert N.cfl_quantifier("conservative") is None
    # the registry text fixes it: existential kinds say 'there is nu0', universal ones 'all/every nu'
    assert KINDS["stable_for_small_cfl"]["quantifier"].startswith("there is nu0")
    cfl = [{"param": "cfl"}]
    assert N.sentence_verdict("VERIFIED", "nu0 = 1/4", cfl, ["stable_for_small_cfl"]) == "VERIFIED"
    assert N.sentence_verdict("VERIFIED", "nu in [0, 1/4]", cfl, ["von_neumann_stable_under_cfl"]) == "NOT_REFUTED"
    assert N.sentence_verdict("VERIFIED", "x", cfl, ["stable_for_small_cfl", "positive_under_cfl"]) == "UNKNOWN"


def test_for_reading_reads_the_reading_fields():
    r = {"narrowing": "c = 1", "narrowed": [{"param": "c", "quantifier": U}],
         "formalization": [{"claim": "consistent_order_p", "negated": False}, {"unformalized": "x"}]}
    assert N.for_reading(r, "VERIFIED") == "NOT_REFUTED"
    assert N.for_reading({**r, "narrowing": None}, "VERIFIED") == "VERIFIED"


# ---------------------------------------------------------------- bench v2, post-hoc

def _posthoc():
    p = Path(__file__).resolve().parent.parent / "benchmark/outside_v2/posthoc.py"
    s = importlib.util.spec_from_file_location("posthoc_v2", p)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


@pytest.fixture(scope="module")
def ph():
    return _posthoc()


def test_v2_p_row_under_the_rule(ph):
    out = ph.narrowing()["P"]
    assert out["before"]["match"] == 14 and out["before"]["wrong"] == 2
    moved = {(m["id"], m["field"]): m for m in out["moved"]}
    for f in ("alone", "with_hypotheses"):
        m = moved["barsukow_uzh_notes:13", f]
        assert (m["before"], m["annotated"], m["sentence_verdict"]) == ("WRONG", "GAP", ["NOT_REFUTED"])
    assert out["moves"] == {"MATCH -> GAP": 14, "WRONG -> GAP": 2}
    assert out["annotated"]["match"] == out["annotated"]["wrong"] == 0
    assert out["unrecorded"] == out["annotated"]          # every annotated narrowing is universal


def test_v2_frozen_scoring_is_unchanged_without_the_flag(ph):
    rows = ph._rows(False, False)
    assert ph.R.tally(rows)["match"] == 14 and all("instance_verdict" not in a for r in rows for a in r["readings"])


def test_posthoc_ssp_verdicts(ph):
    got = {(r["file"], r["name"][:24]): list(r["verdicts"].values())[0] for r in ph.ssp()}
    assert {k[0]: v for k, v in got.items() if not k[0].startswith("ketcheson")} == {
        "cockburn-01-ssp-class.json": "VERIFIED", "cockburn-06-printed-class.json": "REFUTED",
        "gp-04-ssprk33.json": "VERIFIED", "kt-09-family-s2.json": "VERIFIED", "kt-09-family-s3.json": "VERIFIED"}
    assert [v for k, v in got.items() if k[0].startswith("ketcheson")] == ["VERIFIED"] * 3
    assert ph.ssprk33_third_order()
