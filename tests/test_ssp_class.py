"""Class-quantified SSP claims and the value of the SSP coefficient (physverify/schemes/ssp_class.py),
with the exact LP behind them (exactlp.py). No Lean."""

from fractions import Fraction

import pytest

from physverify import schemes
from physverify.schemes import exactlp, ssp_class as SC

SSPRK33 = ["alpha_10 = 1", "beta_10 = 1", "alpha_20 = 3/4", "alpha_21 = 1/4", "beta_20 = 0", "beta_21 = 1/4",
           "alpha_30 = 1/3", "alpha_31 = 0", "alpha_32 = 2/3", "beta_30 = 0", "beta_31 = 0", "beta_32 = 2/3"]
ALL = ["alpha_nonneg", "beta_nonneg", "alpha_row_sums_1", "ratio_c"]
RK4 = {"butcher": {"A": [["0", "0", "0", "0"], ["1/2", "0", "0", "0"], ["0", "1/2", "0", "0"], ["0", "0", "1", "0"]],
                   "b": ["1/6", "1/3", "1/3", "1/6"]}}


def cls(**cfg):
    return SC.ssp_class({"claims": {"ssp_class": cfg}})


def coef(**cfg):
    return SC.ssp_coefficient({"claims": {"ssp_coefficient": cfg}})


def _replay_counterexample(r, s):
    """Recompute the stages of the counterexample from its own arrays and F, in Fractions."""
    ce = r["witness"]["counterexample"]
    alpha = [[Fraction(x) for x in row] for row in ce["alpha"]]
    beta = [[Fraction(x) for x in row] for row in ce["beta"]]
    c, u0 = Fraction(ce["dt/dt_FE"]), Fraction(ce["u0"])
    if ce["S"].startswith("{1}"):
        u = SC.so_stages(alpha, beta, lambda v: Fraction(0), u0, c)
        assert u0 == 1 and any(x != 1 for x in u[1:])
        return
    table = {Fraction(k): Fraction(v) for k, v in ce["F"].items() if k != "elsewhere"}
    F = lambda y: table.get(y, -y)                                  # noqa: E731
    assert u0 >= 0 and all(x < 0 or x + F(x) >= 0 for x in table)   # forward Euler keeps [0, inf) on t in [0, 1]
    u = SC.so_stages(alpha, beta, F, u0, c)
    assert [str(x) for x in u] == ce["stages"] and min(u[1:]) < 0
    assert len(alpha) == s


def test_ssprk33_coefficients_as_a_class_verify_at_c_1():
    r = cls(stages=3, c="1", conditions=SSPRK33)
    assert r["status"] == "VERIFIED"
    assert len(r["witness"]["farkas"]) == 3 * 2 + 6 * 3


def test_ssprk33_class_refuted_above_its_coefficient():
    r = cls(stages=3, c="2", conditions=SSPRK33)
    assert r["status"] == "REFUTED"
    _replay_counterexample(r, 3)


def test_the_standard_family_verifies_with_its_c():
    for c in ("1/3", "1", "5/2"):
        assert cls(stages=3, c=c, families=ALL)["status"] == "VERIFIED", c


def test_farkas_certificates_replay():
    s, c = 2, Fraction(1)
    conds = [q for f in ALL for q in SC.family(f, s, c)]
    vs = SC.names(s)
    for label, tgt in SC.targets(s, c):
        cert = exactlp.farkas(conds, tgt, vs)
        assert cert is not None and exactlp.replay(conds, tgt, vs, cert["multipliers"]) is not None, label


def test_without_beta_nonneg_refuted_with_exact_counterexample():
    conds = ["beta_10 >= 0", "beta_20 >= 0", "beta_30 >= 0", "beta_31 >= 0", "beta_32 >= 0", "beta_21 = -1/2"]
    r = cls(stages=3, c="1/2", families=["alpha_nonneg", "alpha_row_sums_1", "ratio_c"], conditions=conds)
    assert r["status"] == "REFUTED"
    assert r["witness"]["counterexample"]["beta"][1][1] == "-1/2"
    _replay_counterexample(r, 3)


def test_printed_abs_ratio_condition_refuted():
    """|beta| c <= alpha, alpha >= 0, unit row sums: the conditions as printed with no beta >= 0."""
    r = cls(stages=2, c="2", families=["alpha_nonneg", "alpha_row_sums_1", "abs_ratio_c"])
    assert r["status"] == "REFUTED"
    _replay_counterexample(r, 2)


def test_missing_row_sums_refuted_with_the_point_set():
    r = cls(stages=2, c="1", families=["alpha_nonneg", "beta_nonneg", "ratio_c"])
    assert r["status"] == "REFUTED" and r["witness"]["counterexample"]["S"].startswith("{1}")
    _replay_counterexample(r, 2)


@pytest.mark.parametrize("cfg", [dict(c="1", families=ALL),                       # no stage count
                                 dict(stages="s", c="1", families=ALL),
                                 dict(stages=2, c="1", conditions=["alpha_10*beta_10 >= 0"]),  # nonlinear
                                 dict(stages=2, c="1", conditions=["gamma_10 >= 0"]),          # unknown variable
                                 dict(stages=2, c="1", families=ALL, conditions=["alpha_10 = 2"])])  # empty class
def test_unstatable_classes_are_unknown(cfg):
    assert cls(**cfg)["status"] == "UNKNOWN"


def test_rk4_coefficient():
    assert coef(method=RK4, relation="=", value="0")["status"] == "VERIFIED"
    assert coef(method="rk4", relation=">=", value="1/2")["status"] == "REFUTED"


def test_coefficient_values_and_comparisons():
    assert coef(method="ssprk33", relation="=", value="1")["status"] == "VERIFIED"
    assert coef(method="ssprk33", relation=">", value="1")["status"] == "REFUTED"
    assert coef(method="ssprk22", relation=">=", other="rk4")["status"] == "VERIFIED"
    assert coef(method="rk4", relation="=", other="ssprk22")["status"] == "REFUTED"
    # SSPRK(5,4): C is irrational-looking and known in an enclosure of width < 2^-64 near 1.508
    assert coef(method="ssprk54", relation=">=", value="3/2")["status"] == "VERIFIED"
    assert coef(method="ssprk54", relation="<=", value="3/2")["status"] == "REFUTED"


def test_decide_on_enclosures():
    pt, iv = (Fraction(1), Fraction(1)), (Fraction(1), Fraction(2))      # 1, and some x in [1, 2)
    assert SC._decide(">=", iv, pt) is True and SC._decide(">", iv, pt) is None
    assert SC._decide("<", pt, (Fraction(2), Fraction(3))) is True
    assert SC._decide("=", iv, pt) is None and SC._decide("=", iv, (Fraction(2), Fraction(2))) is False


def test_through_the_scheme_checker():
    rep = schemes.check({"name": "class", "named_claims": ["ssp_class_preserves"],
                         "claims": {"ssp_class": {"stages": 3, "c": "1", "conditions": SSPRK33}}})
    assert [v["verdict"] for v in rep["claims"]] == ["VERIFIED"]
    rep = schemes.check({"name": "rk4", "named_claims": ["ssp_coefficient"],
                         "claims": {"ssp_coefficient": {"method": "rk4", "relation": ">=", "value": "1/2"}}})
    assert [v["verdict"] for v in rep["claims"]] == ["REFUTED"]


def test_lp_basics():
    # min x + y subject to x >= 1, y >= 2, x - y = 0: 4 at (2, 2)
    conds = [(Fraction(-1), {"x": Fraction(1)}, ">="), (Fraction(-2), {"y": Fraction(1)}, ">="),
             (Fraction(0), {"x": Fraction(1), "y": Fraction(-1)}, "=")]
    m = exactlp.minimize_affine(conds, (Fraction(0), {"x": Fraction(1), "y": Fraction(1)}), ["x", "y"])
    assert m["status"] == "optimal" and m["value"] == 4 and m["point"] == {"x": 2, "y": 2}
    m = exactlp.minimize_affine(conds, (Fraction(0), {"x": Fraction(-1)}), ["x", "y"])
    assert m["status"] == "unbounded"
    bad = conds + [(Fraction(1), {"x": Fraction(-1)}, ">=")]                                # x <= 1 and x = y >= 2
    assert exactlp.minimize_affine(bad, (Fraction(0), {}), ["x", "y"])["status"] == "infeasible"
