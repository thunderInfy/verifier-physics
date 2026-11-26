"""Tests for the exact refutation of entropy selection by a steady non-entropy step
(checks.steady_nonentropy_step and its row in the claims table)."""
from fractions import Fraction
from pathlib import Path

import pytest

from physverify.schemes import check, checks, claims as C, linear, load, poly as P

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes"
LW = ROOT / "benchmark" / "scheme-claims" / "specs" / "burgers-lax-wendroff.json"
MONOTONE = ["burgers-engquist-osher", "burgers-lax-friedrichs", "burgers-rusanov"]
LAMS = [Fraction(2, 5), Fraction(37, 100), Fraction(1), Fraction(3)]


def _spec(name):
    return load(S / f"{name}.json")


def _march(H, uL, uR, lam, n=8, steps=5):
    """Exact time steps on n cells, jump at the middle interface, transmissive (constant) ghost cells."""
    u = [uL] * (n // 2) + [uR] * (n - n // 2)
    for _ in range(steps):
        g = [u[0]] + u + [u[-1]]
        u = [P.evaluate(H, {"um1": g[i - 1], "u0": g[i], "up1": g[i + 1], "lam": lam}) for i in range(1, n + 1)]
    return u


def test_roe_steady_step_is_exact_and_replays():
    r = checks.steady_nonentropy_step(_spec("broken-burgers-roe-no-entropy-fix"))
    assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
    w = r["witness"]
    uL, uR = Fraction(w["uL"]), Fraction(w["uR"])
    assert (uL, uR) == (-1, 1) and w["found_by"] == "candidate pair"
    assert Fraction(w["f'(uL)"]) < Fraction(w["f'(uR)"]) and w["f''(u)"] == "1"
    H = P.from_expr(checks.update(_spec("broken-burgers-roe-no-entropy-fix")))
    for lam in LAMS:                                 # replay the four identities and march the grid exactly
        for s, t in (((uL, uL, uL), uL), ((uR, uR, uR), uR), ((uL, uL, uR), uL), ((uL, uR, uR), uR)):
            assert P.evaluate(H, dict(zip(checks.STENCIL, s), lam=lam)) == t
        assert _march(H, uL, uR, lam) == [uL] * 4 + [uR] * 4
    assert any("expansion-shock weak solution" in a for a in r["assumptions"])     # conservative, f(-1) = f(1)
    assert any("convex" in a for a in r["assumptions"]) and any("cell interface" in a for a in r["assumptions"])


def test_roe_entropy_claim_refuted_exactly():
    v = {x["claim"]: x for x in check(_spec("broken-burgers-roe-no-entropy-fix"), (100, 200), (200, 400))["claims"]}
    s = v["selects_entropy_solution"]
    assert s["verdict"] == C.REFUTED and s["guarantee"] == C.EXACT and s["decided_by"] == ["steady_nonentropy_step"]
    assert any("steady non-entropy step" in a for a in s["assumes"])
    assert {e["check"]: e["gives"] for e in s["evidence"]}["entropy_rarefaction"] == C.REFUTED_EMPIRICALLY


@pytest.mark.parametrize("name", MONOTONE)
def test_monotone_schemes_have_no_steady_step(name):
    """Crandall-Majda: a monotone conservative consistent scheme has no steady non-entropy step. The
    check finds none, so the two rows never contradict each other; the monotone verdict stands."""
    spec = _spec(name)
    r = checks.steady_nonentropy_step(spec)
    assert r["status"] == checks.UNKNOWN and "proves nothing" in r["detail"] and "0 not decided" in r["detail"]
    H = P.from_expr(checks.update(spec))
    for a, b in checks.STEADY_PAIRS:
        assert any(checks.steady_identities(H, a, b).values())
    v = {x["claim"]: x for x in check(spec, (100, 200), (200, 400))["claims"]}["selects_entropy_solution"]
    assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["monotonicity"]
    assert {e["check"]: e["gives"] for e in v["evidence"]}["steady_nonentropy_step"] == C.UNKNOWN


def test_harten_fix_removes_the_steady_step():
    """Harten's fix gives the sonic interface viscosity delta/2: at (-1, 1) the straddling stencils
    move by -+lam*delta/2 = -+lam/4, so the step is not a fixed point."""
    spec = _spec("burgers-roe-harten-fix")
    assert checks.steady_nonentropy_step(spec)["status"] == checks.UNKNOWN
    res = checks.steady_identities(P.from_expr(checks.update(spec)), Fraction(-1), Fraction(1))
    assert {k: P.show(v) for k, v in res.items() if v} == {"H(uL, uL, uR)": "1/4*lam", "H(uL, uR, uR)": "-1/4*lam"}


def test_lax_wendroff_burgers_has_a_steady_expansion_shock():
    spec = load(LW)
    r = checks.steady_nonentropy_step(spec)
    assert r["status"] == checks.REFUTED and (r["witness"]["uL"], r["witness"]["uR"]) == ("-1", "1")
    H = P.from_expr(checks.update(spec))
    for lam in LAMS:
        assert _march(H, Fraction(-1), Fraction(1), lam) == [-1] * 4 + [1] * 4
    v = {x["claim"]: x for x in check(spec, (100, 200), (200, 400))["claims"]}
    assert v["selects_entropy_solution"]["verdict"] == C.REFUTED


def test_search_is_labelled_and_needs_no_conservation():
    """A non-conservative update with a steady step: the row refutes without a conservation
    precondition. One whose steady step lies off the candidate pairs: the search finds it and says so."""
    spec = {"name": "steady non-conservative", "pde": {"flux": "u^2/2"},
            "scheme": {"update": "u0 - lam*u0*(u0 - um1)*(up1 - u0)"},
            "named_claims": ["selects_entropy_solution"], "claims": {}}
    rep = check(spec)
    r = {x["check"]: x for x in rep["checks"]}
    assert r["conservation"]["status"] == checks.REFUTED
    st = r["steady_nonentropy_step"]
    assert st["status"] == checks.REFUTED and st["witness"]["found_by"] == "candidate pair"
    assert any("may not even be a weak solution" in a for a in st["assumptions"])
    assert rep["claims"][0]["verdict"] == C.REFUTED
    # every pair is steady above; this update is steady only at (-1/3, 3/2), off the candidate pairs
    spec2 = {**spec, "scheme": {"update": "u0 - lam*(up1 - um1)*(u0 + 1/3)*(u0 - 3/2)"}}
    w = checks.steady_nonentropy_step(spec2)["witness"]
    assert (w["uL"], w["uR"], w["found_by"]) == ("-1/3", "3/2", "search over small rationals")


def test_out_of_scope_fluxes():
    assert checks.steady_nonentropy_step(_spec("advection-upwind"))["status"] == checks.NOT_APPLICABLE
    cubic = {"pde": {"flux": "u^3"}, "scheme": {"numerical_flux": "(uL^3 + uR^3)/2"}}   # f'' = 6u, not >= 0 by form
    assert checks.steady_nonentropy_step(cubic)["status"] == checks.NOT_APPLICABLE


def test_polarity_exact_necessary_failure_refutes():
    row = next(r for r in C.CLAIMS["selects_entropy_solution"][1] if r[0] == "steady_nonentropy_step")
    assert row[1] == C.NECESSARY and len(row) == 3 and C.GUARANTEE["steady_nonentropy_step"] == C.EXACT
    table = {"c": ("t", C.CLAIMS["selects_entropy_solution"][1])}
    judge = lambda st: C.judge(["c"], [{"check": k, "status": x, "assumptions": []} for k, x in st.items()], table)[0]
    assert judge({"steady_nonentropy_step": "REFUTED"})["verdict"] == C.REFUTED
    assert judge({"steady_nonentropy_step": "REFUTED"})["guarantee"] == C.EXACT
    for st in ("UNKNOWN", "NOT_APPLICABLE"):
        assert judge({"steady_nonentropy_step": st})["verdict"] == C.UNKNOWN
    assert judge({"steady_nonentropy_step": "VERIFIED"})["verdict"] == C.NOT_REFUTED    # a pass never verifies
    # a monotone scheme with a steady non-entropy step would be a checker bug, and the judge says so loudly
    ok = {"monotonicity": "VERIFIED", "conservation": "VERIFIED", "consistency": "VERIFIED"}
    assert judge({**ok, "steady_nonentropy_step": "REFUTED"})["verdict"] == C.INCONSISTENT


def test_lax_richtmyer_scope_needs_a_periodic_grid():
    """Side fix: periodicity is implicit in the studies; an explicit non-periodic boundary is out of scope."""
    spec = _spec("advection-lax-wendroff")
    assert linear.lax_richtmyer_scope(spec)["status"] == checks.VERIFIED
    out = linear.lax_richtmyer_scope({**spec, "test": {**spec["test"], "boundary": "transmissive"}})
    assert out["status"] == checks.NOT_APPLICABLE and "periodic" in out["detail"]
    premise = next(r for r in C.CLAIMS["converges_order_p"][1] if r[0] == "truncation_order")[2]
    assert "l2" in premise and "L-infinity order is not covered" in premise
