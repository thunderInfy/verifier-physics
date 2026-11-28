"""SSP time stepping (physverify/schemes/ssp.py): exact SSP coefficients, their two certificates, and the
claim `ssp_preserves` on the specs in schemes/ssp. No Lean (the class theorem is lean/PhysVerify/SSP.lean)."""

from fractions import Fraction
from pathlib import Path

import pytest

from physverify import schemes
from physverify.schemes import checks, ssp
from physverify.schemes import univariate as U

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes/ssp"
NEG = {"butcher": {"A": [["0", "0"], ["-20", "0"]], "b": ["41/40", "-1/40"]}}     # second order, negative b2
SSPRK33_BUTCHER = {"butcher": {"A": [["0", "0", "0"], ["1", "0", "0"], ["1/4", "1/4", "0"]],
                               "b": ["1/6", "1/6", "2/3"]}}


@pytest.mark.parametrize("method, C", [("forward_euler", 1), ("ssprk22", 1), ("ssprk33", 1), (SSPRK33_BUTCHER, 1),
                                       ("rk4", 0), (NEG, 0)])
def test_exact_coefficients(method, C):
    c = ssp.coefficient(method)
    assert c["C"] == c["lo"] == c["r"] == C
    assert c["hi"] > C or C == 0


def test_ssprk54_enclosure():
    """C of the printed SSPRK(5,4) is irrational as far as we can tell: an exact enclosure of width < 2^-64
    around 1.50818004918983, and the printed Shu-Osher form's ratio lies in it."""
    c = ssp.coefficient("ssprk54")
    assert c["C"] is None
    assert Fraction("1.508180049189") < c["lo"] < c["hi"] < Fraction("1.508180049190")
    assert c["hi"] - c["lo"] < ssp.EPS
    assert c["r"] <= c["lo"] and c["lo"] - c["r"] < Fraction(1, 10 ** 9)
    form = c["form"]
    assert form["admissible"] and form["c"] <= c["hi"]
    assert abs(float(form["c"]) - 1.50818004918983) < 1e-13


def test_ssprk54_is_fourth_order_to_rounding():
    """The eight order conditions of a fourth-order method hold to the 15 printed digits."""
    K, _, _ = ssp.method_K("ssprk54")
    s = len(K) - 1
    A = [[float(K[i][j]) for j in range(s)] for i in range(s)]
    b = [float(K[s][j]) for j in range(s)]
    c = [sum(row) for row in A]
    Ac = [sum(A[i][j] * c[j] for j in range(s)) for i in range(s)]
    Ac2 = [sum(A[i][j] * c[j] ** 2 for j in range(s)) for i in range(s)]
    AAc = [sum(A[i][j] * Ac[j] for j in range(s)) for i in range(s)]
    conds = [(sum(b), 1), (sum(bi * ci for bi, ci in zip(b, c)), 1 / 2),
             (sum(bi * ci ** 2 for bi, ci in zip(b, c)), 1 / 3), (sum(bi * x for bi, x in zip(b, Ac)), 1 / 6),
             (sum(bi * ci ** 3 for bi, ci in zip(b, c)), 1 / 4), (sum(bi * ci * x for bi, ci, x in zip(b, c, Ac)), 1 / 8),
             (sum(bi * x for bi, x in zip(b, Ac2)), 1 / 12), (sum(bi * x for bi, x in zip(b, AAc)), 1 / 24)]
    assert all(abs(got - want) < 1e-14 for got, want in conds), conds


def test_stability_polynomials():
    K, _, _ = ssp.method_K("rk4")
    assert ssp.stability_polynomial(K) == [1, 1, Fraction(1, 2), Fraction(1, 6), Fraction(1, 24)]
    K, _, _ = ssp.method_K(NEG)                     # second order: same R(z) as any two-stage second-order method
    assert ssp.stability_polynomial(K) == [1, 1, Fraction(1, 2)]


@pytest.mark.parametrize("method", ["ssprk22", "ssprk33", "ssprk54", SSPRK33_BUTCHER])
def test_certificate_is_an_admissible_form_of_the_same_method(method):
    c = ssp.coefficient(method)
    cert, K = c["certificate"], ssp.method_K(method)[0]
    assert ssp.shu_osher_K(cert["alpha"], cert["beta"]) == K
    ratio = ssp.shu_osher_ratio(cert["alpha"], cert["beta"])
    assert ratio["admissible"] and ratio["c"] >= c["r"] > 0
    with pytest.raises(AssertionError):           # above C there is no such form
        ssp.shu_osher_certificate(K, c["hi"])


def test_every_entry_is_nonneg_up_to_C_and_one_fails_above():
    """The root isolation against direct decisions: every entry of v(r), P(r) is >= 0 on [0, lo]
    (square-free + Sturm), and some entry is < 0 at hi."""
    for m in ("ssprk22", "ssprk33", "ssprk54"):
        c = ssp.coefficient(m)
        K = ssp.method_K(m)[0]
        assert all(U.nonneg_on(p, 0, c["lo"])["nonneg"] for _, p in ssp._entries(K)), m
        v, Pm = ssp.am_at(K, c["hi"])
        assert min(v + [x for row in Pm for x in row]) < 0, m


def _check_witness(K, w):
    """Recompute the class witness from K alone: F is forward-Euler admissible on [0, inf) with tau = 1,
    and one step with dt = w["dt/tau"] from u0 >= 0 has a negative stage."""
    table = {Fraction(x): Fraction(f) for x, f in w["F at the stage points"].items()}
    F = lambda x: table.get(x, -x)
    assert w["u0"] >= 0
    for x, f in table.items():                      # x + t F(x) >= 0 for t in [0, 1] wherever x >= 0
        assert x < 0 or (x + f >= 0 and x >= 0)
    Y = ssp.butcher_stages(K, F, w["u0"], w["dt/tau"])
    assert Y == w["stages"] and min(Y) < 0
    return Y


@pytest.mark.parametrize("method", ["rk4", NEG, "ssprk33", "ssprk54"])
def test_class_witness(method):
    """Above C (at dt = hi tau; for C = 0 at some small dt) an explicit admissible F breaks positivity,
    of the new step itself for these methods."""
    K = ssp.method_K(method)[0]
    w = ssp.coefficient(method)["witness"]
    Y = _check_witness(K, w)
    assert w["is the new step"] and Y[-1] < 0


def test_negative_beta_form():
    """A Shu-Osher form with a negative beta is not admissible for the lemma, and the method has C = 0."""
    so = {"shu_osher": {"alpha": [["1"], ["1", "0"]], "beta": [["-20"], ["41/40", "-1/40"]]}}
    K, _, _ = ssp.method_K(so)
    assert K == ssp.method_K(NEG)[0]
    c = ssp.coefficient(so)
    assert not c["form"]["admissible"] and "beta" in c["form"]["reason"]
    assert c["C"] == 0


def test_malformed_methods():
    with pytest.raises(ssp.Unsupported, match="implicit"):
        ssp.butcher_K([["1/2"]], ["1"])
    with pytest.raises(ssp.Unsupported, match="sums to"):
        ssp.shu_osher_K([["1"], ["1/2", "1/4"]], [["1"], ["0", "1/2"]])


def test_simplest_between():
    assert ssp._simplest_between(Fraction(1, 3), Fraction(1, 2)) == Fraction(2, 5)
    assert ssp._simplest_between(Fraction(0), Fraction(1, 2)) == Fraction(1, 3)
    assert ssp._simplest_between(Fraction(3, 2), Fraction(7, 2)) == 2


def test_first_sign_change():
    f = ssp.first_sign_change([Fraction(1), Fraction(-1)])                       # 1 - r
    assert f["exact"] == f["lo"] == 1 < f["hi"]
    assert ssp.first_sign_change([Fraction(0), Fraction(-1)])["kind"] == "zero"
    assert ssp.first_sign_change([Fraction(1), Fraction(0), Fraction(1)])["kind"] == "never"
    # (1 - r)^2 touches 0 at 1 without changing sign; (2 - r) does at 2
    f = ssp.first_sign_change(U.mul(U.power([Fraction(1), Fraction(-1)], 2), [Fraction(2), Fraction(-1)]))
    assert f["exact"] == 2
    f = ssp.first_sign_change([Fraction(2), Fraction(0), Fraction(-1)])          # sqrt 2
    assert f["exact"] is None and f["lo"] ** 2 < 2 < f["hi"] ** 2


# ---------------------------------------------------------------- the claim on the specs

EXPECTED = {
    "advection-upwind-ssprk33": ("VERIFIED", {"ssp": "VERIFIED", "ssp_linear": "VERIFIED"}),
    # C = 0, so the class theorem says nothing; for a linear scheme the exact decision verifies it anyway
    "advection-upwind-rk4": ("VERIFIED", {"ssp": "NOT_APPLICABLE", "ssp_linear": "VERIFIED"}),
    "broken-advection-upwind-ssprk33-wide-cfl": ("REFUTED", {"ssp": "UNKNOWN", "ssp_linear": "REFUTED",
                                                            "ssp_violation": "REFUTED"}),
    "advection-muscl-minmod-ssprk33": ("VERIFIED", {"ssp": "VERIFIED", "ssp_linear": "NOT_APPLICABLE"}),
    "advection-muscl-minmod-ssprk54": ("VERIFIED", {"ssp": "VERIFIED"}),
    "advection-muscl-minmod-ssprk33-max-principle": ("VERIFIED", {"ssp": "VERIFIED"}),
    # not SSP and nonlinear: no theorem applies and the exact search finds no violating step
    "advection-muscl-minmod-rk4": ("UNKNOWN", {"ssp": "NOT_APPLICABLE", "ssp_violation": "UNKNOWN"}),
    "advection-muscl-minmod-negative-weights": ("UNKNOWN", {"ssp": "NOT_APPLICABLE", "ssp_violation": "UNKNOWN"}),
}


def test_the_spec_set():
    assert {p.stem for p in S.glob("*.json")} == set(EXPECTED)


@pytest.mark.parametrize("stem", sorted(EXPECTED))
def test_spec_verdicts(stem):
    rep = schemes.check(schemes.load(S / f"{stem}.json"))
    verdict = {v["claim"]: v for v in rep["claims"]}["ssp_preserves"]
    status = {r["check"]: r for r in rep["checks"]}
    want, checks_want = EXPECTED[stem]
    assert verdict["verdict"] == want
    assert {k: status[k]["status"] for k in checks_want} == checks_want
    if status["ssp"]["status"] == "NOT_APPLICABLE":
        assert "C = 0" in status["ssp"]["detail"]
    if status["ssp"]["status"] == "VERIFIED":
        assert ssp.LEAN in status["ssp"]["detail"]


def test_refutation_data_are_exact():
    rep = schemes.check(schemes.load(S / "broken-advection-upwind-ssprk33-wide-cfl.json"))
    r = {r["check"]: r for r in rep["checks"]}["ssp_violation"]
    w = r["witness"]
    spec = schemes.load(S / "broken-advection-upwind-ssprk33-wide-cfl.json")
    v = ssp.rk_step(spec, ssp.method_K("ssprk33")[0], [Fraction(x) for x in w["periodic state u^n"]], Fraction(w["lam"]))
    assert [str(x) for x in v] == w["u^{n+1}"] and min(v) < 0


def test_rk_step_matches_the_stability_polynomial():
    """Stage by stage, RK4 on upwind is R(nu D) applied to the data."""
    spec = schemes.load(S / "advection-upwind-rk4.json")
    u = [Fraction(x) for x in (0, 1, 3, -2, 5, 0, 0, 1, 2)]
    nu = Fraction(3, 7)
    v = ssp.rk_step(spec, ssp.method_K("rk4")[0], u, nu)
    acc, p = list(u), list(u)
    for g in (1, Fraction(1, 2), Fraction(1, 6), Fraction(1, 24)):
        p = [-nu * (p[i] - p[i - 1]) for i in range(len(u))]                 # (nu D)^j u, D the upwind difference
        acc = [a + g * x for a, x in zip(acc, p)]
    assert v == acc


def test_forward_euler_form():
    assert ssp.forward_euler_form(schemes.load(ROOT / "schemes/advection-upwind.json")) == ""
    assert "lam" in ssp.forward_euler_form(schemes.load(ROOT / "schemes/limiters/advection-minmod.json"))
    assert ssp.forward_euler_form(schemes.load(ROOT / "schemes/advection-lax-wendroff.json"))
    spec = {"pde": {"flux": "u"}, "scheme": {"update": "u0 - lam*(u0 - um1)"}}
    assert ssp.forward_euler_form(spec) == ""
    spec = {"pde": {"flux": "u"}, "scheme": {"update": "u0 - lam*(u0 - um1) + lam^2*(up1 - 2*u0 + um1)/2"}}
    assert ssp.forward_euler_form(spec)


def test_not_a_forward_euler_step_is_not_applicable():
    spec = schemes.load(ROOT / "schemes/limiters/advection-minmod.json")
    spec = {**spec, "named_claims": ["ssp_preserves"],
            "claims": {**spec["claims"], "ssp": {"method": "ssprk33", "property": "tvd", "cfl": "1/2"}}}
    rep = schemes.check(spec)
    st = {r["check"]: r["status"] for r in rep["checks"]}
    assert st["ssp"] == st["ssp_linear"] == st["ssp_violation"] == checks.NOT_APPLICABLE
    assert rep["claims"][0]["verdict"] == "UNKNOWN"
