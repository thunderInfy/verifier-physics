"""Tests for the discrete-scheme checker (physverify/schemes)."""
import random
from fractions import Fraction
from math import factorial
from pathlib import Path

import numpy as np
import pytest

from physverify.expr import parse
from physverify.schemes import (FAILURES, check, checks, claims as C, convergence, entropy, linear, load, poly as P,
                                render, shock)

S = Path(__file__).resolve().parent.parent / "schemes"
BURGERS = ["burgers-lax-friedrichs", "burgers-engquist-osher", "burgers-rusanov"]
SHOCK_GRIDS = (100, 200, 400, 800)  # the CLI refines to N = 3200
RAREFACTION_GRIDS = (200, 400)      # the CLI refines to N = 1600
CORRECT = ["advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff",
           "burgers-lax-friedrichs", "burgers-engquist-osher", "burgers-rusanov", "burgers-roe-harten-fix"]
# broken spec -> the checks that must catch it (and nothing else may fail)
BROKEN = {"broken-advection-inconsistent-flux": {"consistency", "order/combined"},
          "broken-burgers-scaled-flux": {"consistency", "order/combined"},
          "broken-burgers-nonconservative": {"conservation", "shock_speed"},
          "broken-burgers-roe-no-entropy-fix": {"entropy_stability", "entropy_rarefaction", "monotonicity",
                                                       "steady_nonentropy_step"},
          "broken-advection-lax-friedrichs-wide-cfl": {"positivity", "monotonicity", "von_neumann"},
          "broken-advection-lax-wendroff-monotone": {"monotonicity"},
          "broken-burgers-rusanov-wide-cfl": {"monotonicity"},
          "broken-advection-downwind": {"positivity"},
          # halving Lax-Wendroff's diffusion leaves it first order and unstable for every nu != 0
          "broken-advection-fake-second-order": {"order/combined", "truncation_order", "von_neumann"},
          "broken-advection-ftcs": {"von_neumann", "order/combined"}}


def _p(s):
    return P.from_expr(parse(s))


@pytest.fixture(scope="module")
def reports():
    return {name: check(load(S / f"{name}.json"), SHOCK_GRIDS, RAREFACTION_GRIDS) for name in CORRECT + list(BROKEN)}


@pytest.fixture(scope="module")
def results(reports):
    return {name: {r["check"]: r for r in rep["checks"]} for name, rep in reports.items()}


@pytest.fixture(scope="module")
def verdicts(reports):
    return {name: {v["claim"]: v for v in rep["claims"]} for name, rep in reports.items()}


def test_every_spec_on_disk_is_covered():
    assert {p.stem for p in S.glob("*.json")} == set(CORRECT) | set(BROKEN)


@pytest.mark.parametrize("name", CORRECT)
def test_correct_schemes_pass(results, name):
    r = results[name]
    assert r["consistency"]["status"] == checks.VERIFIED
    assert r["conservation"]["status"] == checks.VERIFIED
    assert r["positivity"]["status"] in (checks.VERIFIED, checks.NOT_APPLICABLE)
    orders = [v for k, v in r.items() if k.startswith("order/")]
    assert orders and all(v["status"] == convergence.NOT_REFUTED for v in orders)
    if name.startswith("burgers"):
        assert r["shock_speed"]["status"] == convergence.NOT_REFUTED
        assert r["entropy_rarefaction"]["status"] == convergence.NOT_REFUTED
    if name in BURGERS:
        assert r["entropy_stability"]["status"] == checks.VERIFIED
        assert "semi-discrete" in r["entropy_stability"]["guarantee"]


@pytest.mark.parametrize("name", sorted(BROKEN))
def test_broken_schemes_caught_by_the_right_check(results, name):
    failed = {k for k, v in results[name].items() if v["status"] in FAILURES}
    assert failed == BROKEN[name]


def test_expected_orders_and_study_labels(results):
    lw = results["advection-lax-wendroff"]["order/combined"]
    assert "claimed 2" in lw["detail"] and "empirical" in lw["guarantee"]
    up = results["advection-upwind"]
    assert up["order/space"]["witness"]["study"].startswith("space: method of lines")
    assert up["order/time"]["witness"]["study"].startswith("time: forward Euler")
    # a dt/dx-dependent flux cannot be split into space and time studies
    assert convergence._mol_ok(checks.update(load(S / "advection-lax-friedrichs.json")))[0] is False


def test_superconvergence_is_suspicious_not_a_pass():
    spec = load(S / "advection-lax-wendroff.json")
    spec["claims"]["order"] = {"combined": 1}
    (r,) = convergence.studies(spec)
    assert r["status"] == convergence.SUSPICIOUS


def test_refuted_claims_carry_exact_witnesses(results):
    c = results["broken-advection-inconsistent-flux"]["consistency"]["witness"]
    assert c["point"] == {"u": "1"} and Fraction(c["residual_value"]) == 2      # F(1,1) = 1, f(1) = -1
    p = results["broken-advection-lax-friedrichs-wide-cfl"]["positivity"]["witness"]
    assert p["offending"] == "up1" and p["violating_nu"] == "11/10" and Fraction(p["value"]) < 0
    w = results["broken-burgers-nonconservative"]["conservation"]["witness"]
    H = P.from_expr(checks.update(load(S / "broken-burgers-nonconservative.json")))
    d = checks.periodic_change(H, [Fraction(s) for s in w["state"]], Fraction(w["lam"]))
    assert d == Fraction(w["sum_change"]) != 0


def test_positivity_coefficients_are_exact(results):
    w = results["advection-lax-friedrichs"]["positivity"]["witness"]
    assert w["coefficients"] == {"um1": "1/2*nu + 1/2", "u0": "0", "up1": "-1/2*nu + 1/2"}
    burgers = load(S / "burgers-lax-friedrichs.json")
    burgers["claims"]["positive_cfl"] = ["0", "1"]
    r = checks.positivity(burgers)
    assert r["status"] == checks.NOT_APPLICABLE and "out of scope" in r["detail"]


def test_bernstein_certifies_nonlinear_coefficients():
    # nu^2 - nu + 1/4 = (nu - 1/2)^2 >= 0 is not decided by endpoints alone
    assert min(checks.bernstein([Fraction(1, 4), Fraction(-1), Fraction(1)], Fraction(0), Fraction(1))) < 0
    assert min(checks.bernstein([Fraction(1, 4), Fraction(-1), Fraction(1)], Fraction(1), Fraction(2))) >= 0
    # 1 - nu^2 >= 0 on [-1, 1]
    assert min(checks.bernstein([Fraction(1), Fraction(0), Fraction(-1)], Fraction(-1), Fraction(1))) >= 0


@pytest.mark.parametrize("name", CORRECT)
def test_conservation_on_random_rational_data(name):
    """Tests the checker: a VERIFIED telescoping proof must agree with exact random data."""
    H = P.from_expr(checks.update(load(S / f"{name}.json")))
    rng = random.Random(name)
    for n in (3, 5, 8):
        state = [Fraction(rng.randint(-50, 50), rng.randint(1, 9)) for _ in range(n)]
        assert checks.periodic_change(H, state, Fraction(rng.randint(1, 9), rng.randint(1, 9))) == 0


def test_normal_form():
    assert P.add(_p("(a + b)^2"), _p("a^2 + 2*a*b + b^2"), -1) == {}
    assert P.add(_p("sqrt(u^2)^2"), _p("u^2"), -1) == {}
    assert P.add(_p("lam*(1/lam)"), P.const(1), -1) == {}
    assert P.evaluate(_p("sqrt(u^2)"), {"u": Fraction(-3, 2)}) == Fraction(3, 2)
    assert P.evaluate(_p("sqrt(u^2 + 1)"), {"u": Fraction(1)}) is None             # irrational: no verdict
    for bad in ("sqrt(u)", "sin(u)", "1/(u + 1)", "u^(1/2)"):
        with pytest.raises(P.Undecided):
            _p(bad)


def test_undecidable_flux_is_unknown_not_a_verdict():
    spec = {"name": "t", "pde": {"flux": "u^2/2"}, "scheme": {"numerical_flux": "sin(uL)"}}
    assert checks.consistency(spec)["status"] == checks.UNKNOWN
    assert checks.conservation(spec)["status"] == checks.UNKNOWN


def test_burgers_exact_solution_satisfies_characteristics():
    pr = {"kind": "burgers-sine", "mean": 0.5, "amplitude": 0.25}
    x = np.linspace(0, 1, 101)
    u = convergence.exact(pr, x, 0.3)
    assert np.max(np.abs(u - 0.5 - 0.25 * np.sin(2 * np.pi * (x - 0.3 * u)))) < 1e-14
    with pytest.raises(AssertionError):
        convergence.exact(pr, x, 1.0)                                              # after the shock


def test_three_checkers_one_claim(results):
    """Benchmark: one structural fact, conservation, seen three ways. The exact check decides it; the
    smooth convergence study cannot see it; the late-window shock speed sees its consequence, but only
    as a necessary condition (the non-conservative scheme gets (1, -1) right by accident)."""
    r = results["broken-burgers-nonconservative"]
    assert r["conservation"]["status"] == checks.REFUTED and r["conservation"]["guarantee"] == checks.EXACT
    assert r["order/combined"]["status"] == convergence.NOT_REFUTED
    sh = r["shock_speed"]
    assert sh["status"] == convergence.REFUTED_EMPIRICALLY and "empirical" in sh["guarantee"]
    cases = dict(d.split(": ", 1) for d in sh["detail"].removeprefix("(uL, uR) = ").split("; (uL, uR) = "))
    assert [k for k, v in cases.items() if "settled at a non-zero value" in v] == ["(1, 0)", "(2, 1/2)", "(1, -1/2)"]
    assert "settled" not in cases["(1, -1)"]                                      # right speed, by accident
    for name in BURGERS:
        assert all(results[name][k]["status"] in (checks.VERIFIED, convergence.NOT_REFUTED)
                   for k in ("conservation", "order/combined", "shock_speed"))


def test_shock_speed_numbers():
    spec = load(S / "broken-burgers-nonconservative.json")
    assert shock.rh_speed(spec, Fraction(2), Fraction(1, 2)) == Fraction(5, 4)
    assert shock.rh_speed(spec, Fraction(1), Fraction(-1, 2)) == Fraction(1, 4)
    H = checks.update(spec)
    # u = 0 is a fixed point of this update, so the (1, 0) step never moves: speed 0, not 1/2
    # (the slope of a constant position is 0 up to least-squares round-off)
    assert np.max(np.abs(shock.run(H, 1.0, 0.0, 0.25, 1.0, 0.8, 200)["late"])) < 1e-14
    # transonic data: the step 1 | uR < 0 is a fixed point too, right for (1, -1), wrong for (1, -1/2)
    assert np.max(np.abs(shock.run(H, 1.0, -1.0, 0.25, 0.5, 0.8, 200)["late"])) < 1e-14
    assert np.max(np.abs(shock.run(H, 1.0, -0.5, 0.25, 0.5, 0.8, 200)["late"])) < 1e-14
    # (2, 1/2): the speed settles near 0.98, not 5/4, on every grid and at every level
    for n in (200, 800):
        assert np.all(np.abs(np.array(shock.run(H, 2.0, 0.5, 0.25, 0.4, 0.4, n)["late"]) - 0.983) < 0.002)


def test_late_window_removes_the_start_up_offset():
    """Over [0, T] a conservative scheme shows an O(dx) error (the step relaxing into a profile shifts
    the crossing); over [T/2, T] the profile translates at the Rankine-Hugoniot speed, at every level."""
    lf = checks.update(load(S / "burgers-lax-friedrichs.json"))
    rows = [shock.run(lf, 2.0, 0.5, 0.25, 0.4, 0.4, n) for n in (200, 400)]
    full = [abs(r["full"] - 1.25) for r in rows]
    assert 0.45 < full[1] / full[0] < 0.55 and full[1] > 1e-4                    # offset / T ~ dx
    late = [np.abs(np.array(r["late"]) - 1.25) for r in rows]
    assert np.all(late[1] < 0.3 * late[0]) and np.all(late[1] < 0.5 * full[1])
    assert np.all(late[1] < shock.tol(rows[1]) / 50)


@pytest.mark.parametrize("name", ["burgers-engquist-osher", "burgers-rusanov"])
def test_late_window_speed_agrees_across_levels(name):
    """A conservative scheme's profile translates rigidly: the late-window speed is the same at
    levels 0.2, 0.5 and 0.8 (here on the asymmetric transonic case, where the window does not move
    the profile a whole number of cells at N = 200)."""
    H = checks.update(load(S / f"{name}.json"))
    r = shock.run(H, 1.0, -0.5, 0.25, 0.5, 0.8, 200)
    e = np.array(r["late"]) - 0.25
    assert np.ptp(e) < shock.tol(r) / 10 and np.all(np.abs(e) < shock.tol(r) / 10)
    assert abs(r["endpoints"] - 0.25) > 1e-4                                      # phase wobble, not round-off
    assert shock.verdict([r, r], 0.25)[0] == convergence.NOT_REFUTED
    assert shock.verdict([r, r], 0.3)[0] == convergence.REFUTED_EMPIRICALLY


def test_crossing_estimator():
    u = np.array([2.0, 2.0, 1.25, 0.5, 0.5])
    assert shock.crossing(u, 1.25, 0.2) == (0.5, 1)                               # cell 2 centre
    assert shock.crossing(np.array([2.0, 2.0, 0.5, 0.5]), 1.25, 0.25)[0] == 0.5   # interface


# ---------------------------------------------------------------- entropy

def _flux_q(spec):
    """Q(uL, uR, lam) = -(uR - uL)(F - F*) for Burgers' u^2/2 entropy, recomputed independently."""
    F = P.from_expr(checks.numerical_flux(spec))
    Fstar = _p("(uL^2 + uL*uR + uR^2)/6")
    return P.scale(P.mul(_p("uR - uL"), P.add(F, Fstar, -1)), -1)


def test_divide_difference_and_nonneg_by_form():
    q = P.divide_difference(_p("(uR - uL)^2*(uL + 3*uR^2)"), "uL", "uR", 2)
    assert P.add(q, _p("uL + 3*uR^2"), -1) == {}
    assert P.divide_difference(_p("uR^2 - uL"), "uL", "uR", 1) is None
    assert P.divide_difference(_p("uR^3 - uL^3"), "uL", "uR", 2) is None
    assert P.nonneg_by_form(_p("u^2/lam + sqrt(u^2)"), positive={"lam"})
    assert not P.nonneg_by_form(_p("u^2/lam"))
    assert not P.nonneg_by_form(_p("a*b"), nonneg={"a"})
    assert P.nonneg_by_form(_p("a*b^2"), nonneg={"a"})


def test_sign_cells_cover_and_agree():
    """On each closed sign cell the polynomial equals the flux (checked at exact rational points)."""
    F = checks.numerical_flux(load(S / "burgers-rusanov.json"))
    cells = checks.sign_cells(F)
    assert len(cells) == 8
    full = P.from_expr(F)
    rng = random.Random(3)
    for _ in range(300):
        pt = {"uL": Fraction(rng.randint(-9, 9), rng.randint(1, 4)), "uR": Fraction(rng.randint(-9, 9), rng.randint(1, 4))}
        inside = [p for p, atoms in cells if all(P.evaluate(a, pt) >= 0 for a in atoms)]
        assert inside and all(P.evaluate(p, pt) == P.evaluate(full, pt) for p in inside)


def test_roe_entropy_counterexample(results):
    """Third rung: Roe without a fix is consistent and conservative but not entropy stable; the
    exact check gives the expansion pair (-1, 1), where the interface produces entropy 2/3."""
    r = results["broken-burgers-roe-no-entropy-fix"]
    assert r["consistency"]["status"] == r["conservation"]["status"] == checks.VERIFIED
    assert r["shock_speed"]["status"] == convergence.NOT_REFUTED
    e = r["entropy_stability"]
    assert e["status"] == checks.REFUTED and "semi-discrete" in e["guarantee"]
    w = e["witness"]["counterexample"]
    assert w["point"] == {"uL": "-1", "uR": "1"} and Fraction(w["Q"]) == Fraction(-2, 3)
    pt = {k: Fraction(v) for k, v in w["point"].items()}
    assert P.evaluate(_flux_q(load(S / "broken-burgers-roe-no-entropy-fix.json")), pt) == Fraction(-2, 3)
    assert e["witness"]["F_star = [psi]/[v]"] == "1/6*uL*uR + 1/6*uL^2 + 1/6*uR^2"


@pytest.mark.parametrize("name", BURGERS)
def test_entropy_certificates_hold_at_rational_points(results, name):
    """Tests the checker: a VERIFIED entropy certificate must agree with exact random data, and every
    recorded cell identity Q = (uR - uL)^2 D must hold."""
    spec = load(S / f"{name}.json")
    Q = _flux_q(spec)
    cfl = Fraction(spec["claims"]["entropy_stability"].get("cfl", 10 ** 9))
    rng = random.Random(name)
    n = 0
    while n < 300:
        pt = {"uL": Fraction(rng.randint(-30, 30), rng.randint(1, 9)), "uR": Fraction(rng.randint(-30, 30), rng.randint(1, 9)),
              "lam": Fraction(rng.randint(1, 9), rng.randint(1, 9))}
        if pt["lam"] * max(abs(pt["uL"]), abs(pt["uR"])) <= cfl:
            assert P.evaluate(Q, pt) >= 0
            n += 1
    for cell in results[name]["entropy_stability"]["witness"].get("cells", []):
        if "D = Q/(uR - uL)^2" in cell:
            Dc, Qc = _p(cell["D = Q/(uR - uL)^2"]), _p(cell["Q"])
            assert P.add(Qc, P.mul(_p("(uR - uL)^2"), Dc), -1) == {}


def test_lax_friedrichs_entropy_needs_the_cfl_bound():
    """D = 1/(2 lam) - (uR - uL)/12, so LxF is entropy stable iff lam*(uR - uL) <= 6: VERIFIED with
    lam*|u| <= 3, REFUTED with lam*|u| <= 4 and with no bound."""
    spec = load(S / "burgers-lax-friedrichs.json")
    assert checks.entropy_stability(spec)["witness"]["D = Q/(uR - uL)^2"] == "1/2*lam^-1 + 1/12*uL - 1/12*uR"
    for cfl, status in (("3", checks.VERIFIED), ("4", checks.REFUTED), (None, checks.REFUTED)):
        spec["claims"]["entropy_stability"] = {"cfl": cfl} if cfl else {}
        r = checks.entropy_stability(spec)
        assert r["status"] == status
        if status == checks.REFUTED:
            pt = {k: Fraction(v) for k, v in r["witness"]["counterexample"]["point"].items()}
            assert P.evaluate(_flux_q(spec), pt) < 0
            assert pt["lam"] * max(abs(pt["uL"]), abs(pt["uR"])) <= int(cfl or 10 ** 9)


def test_entropy_stability_is_sufficient_not_necessary(results):
    """Harten's fix (delta = 1/2) gives the rarefaction, yet fails Tadmor's inequality at (-1, 1):
    its sonic viscosity delta/2 is below (uR - uL)/6 there. So REFUTED here does not mean a wrong limit."""
    assert results["burgers-roe-harten-fix"]["entropy_rarefaction"]["status"] == convergence.NOT_REFUTED
    spec = load(S / "burgers-roe-harten-fix.json")
    spec["claims"]["entropy_stability"] = {}
    r = checks.entropy_stability(spec)
    assert r["status"] == checks.REFUTED and r["witness"]["counterexample"]["point"] == {"uL": "-1", "uR": "1"}
    assert Fraction(r["witness"]["counterexample"]["Q"]) == Fraction(-1, 6)


def test_entropy_outside_the_fragment_is_unknown():
    spec = load(S / "burgers-engquist-osher.json")
    spec["claims"]["entropy_stability"] = {"eta": "u^4/4", "q": "u^5/5"}       # [v]/(uR - uL) not constant
    assert checks.entropy_stability(spec)["status"] == checks.UNKNOWN
    spec["claims"]["entropy_stability"] = {"eta": "u^2/2", "q": "u^3/2"}       # not an entropy pair
    r = checks.entropy_stability(spec)
    assert r["status"] == checks.UNKNOWN and "not an entropy pair" in r["detail"]
    adv = load(S / "advection-upwind.json")
    adv["claims"]["entropy_stability"] = {}
    assert checks.entropy_stability(adv)["status"] == checks.UNKNOWN            # no default pair for a*u


def test_roe_keeps_the_expansion_shock():
    """(-1, 1) is a fixed point of Roe's update: the L1 error is the area between step and fan, T,
    at both dt/dx (2/5 and the incommensurate 37/100). On (-1/2, 1) Roe keeps a stationary jump
    -1/2 | 1/2 and fans out above it; that limit's L1 error is T/4 = 1/16, which the error approaches."""
    H = checks.update(load(S / "broken-burgers-roe-no-entropy-fix.json"))
    for lam in (0.4, 0.37):
        assert entropy.run(H, -1.0, 1.0, 0.5, 0.25, lam, 200)["L1"] == 0.25
        e = [entropy.run(H, -0.5, 1.0, 0.5, 0.25, lam, n) for n in (200, 400)]
        assert 1 / 16 < e[1]["L1"] < e[0]["L1"] < 1 / 16 + 0.008 and abs(e[1]["max_jump"] - 1) < 0.01
    eo = checks.update(load(S / "burgers-engquist-osher.json"))
    e = [entropy.run(eo, -1.0, 1.0, 0.5, 0.25, 0.37, n)["L1"] for n in (200, 400)]
    assert 0.6 < np.log2(e[0] / e[1]) < 0.9


# ---------------------------------------------------------------- claims vs checks

# spec -> the named claims it must fail, with the verdict; every other claim it makes must not fail
FAILING_CLAIMS = {"broken-advection-inconsistent-flux": {"consistent": C.REFUTED, "converges_order_p": C.REFUTED_EMPIRICALLY},
                  "broken-burgers-scaled-flux": {"consistent": C.REFUTED, "converges_order_p": C.REFUTED_EMPIRICALLY},
                  "broken-burgers-nonconservative": {"conservative": C.REFUTED, "correct_shock_speed": C.REFUTED_EMPIRICALLY},
                  "broken-burgers-roe-no-entropy-fix": {"entropy_stable_tadmor": C.REFUTED,
                                                        "selects_entropy_solution": C.REFUTED,
                                                        "monotone_under_cfl": C.REFUTED},
                  "broken-advection-lax-friedrichs-wide-cfl": {"positive_under_cfl": C.REFUTED,
                                                               "monotone_under_cfl": C.REFUTED,
                                                               "von_neumann_stable_under_cfl": C.REFUTED},
                  "broken-advection-lax-wendroff-monotone": {"monotone_under_cfl": C.REFUTED},
                  "broken-burgers-rusanov-wide-cfl": {"monotone_under_cfl": C.REFUTED},
                  "broken-advection-downwind": {"positive_under_cfl": C.REFUTED},
                  "broken-advection-fake-second-order": {"converges_order_p": C.REFUTED_EMPIRICALLY,
                                                         "consistent_order_p": C.REFUTED,
                                                         "von_neumann_stable_under_cfl": C.REFUTED},
                  "broken-advection-ftcs": {"von_neumann_stable_under_cfl": C.REFUTED,
                                            "converges_order_p": C.REFUTED_EMPIRICALLY}}

# (relation, raw status) -> verdict, for an exact check (conservation) and an empirical one (shock_speed)
EXACT_CASES = {(C.SUFFICIENT, "VERIFIED"): C.VERIFIED, (C.SUFFICIENT, "REFUTED"): C.UNKNOWN,
               (C.NECESSARY, "VERIFIED"): C.NOT_REFUTED, (C.NECESSARY, "REFUTED"): C.REFUTED,
               (C.EQUIVALENT, "VERIFIED"): C.VERIFIED, (C.EQUIVALENT, "REFUTED"): C.REFUTED}
EMPIRICAL_CASES = {(C.SUFFICIENT, "NOT_REFUTED"): C.NOT_REFUTED, (C.SUFFICIENT, "REFUTED_EMPIRICALLY"): C.UNKNOWN,
                   (C.NECESSARY, "NOT_REFUTED"): C.NOT_REFUTED, (C.NECESSARY, "REFUTED_EMPIRICALLY"): C.REFUTED_EMPIRICALLY,
                   (C.EQUIVALENT, "NOT_REFUTED"): C.NOT_REFUTED,
                   (C.EQUIVALENT, "REFUTED_EMPIRICALLY"): C.REFUTED_EMPIRICALLY,
                   # an empirical check cannot promote itself: the table, not the result, fixes its strength
                   (C.EQUIVALENT, "VERIFIED"): C.NOT_REFUTED, (C.NECESSARY, "REFUTED"): C.REFUTED_EMPIRICALLY}
for rel in (C.SUFFICIENT, C.NECESSARY, C.EQUIVALENT):
    for st in ("UNKNOWN", "NOT_APPLICABLE"):
        EXACT_CASES[rel, st] = EMPIRICAL_CASES[rel, st] = C.UNKNOWN
    EMPIRICAL_CASES[rel, "SUSPICIOUS"] = C.SUSPICIOUS


def _judge(links, statuses):
    table = {"c": ("test claim", tuple((chk, rel, "") for chk, rel in links))}
    results = [{"check": chk, "status": st, "assumptions": []} for chk, st in statuses.items()]
    return C.judge(["c"], results, table)[0]


@pytest.mark.parametrize("check_name,cases", [("conservation", EXACT_CASES), ("shock_speed", EMPIRICAL_CASES)])
def test_every_relation_outcome_pair(check_name, cases):
    for (rel, status), want in cases.items():
        v = _judge([(check_name, rel)], {check_name: status})
        assert v["verdict"] == want, (check_name, rel, status)
        assert v["guarantee"] == (C.EXACT if want in (C.VERIFIED, C.REFUTED) else
                                  "" if want == C.UNKNOWN else C.EMPIRICAL)


def test_aggregation_over_several_checks():
    links = [("conservation", C.EQUIVALENT), ("shock_speed", C.NECESSARY)]
    assert _judge(links, {"conservation": "REFUTED", "shock_speed": "REFUTED_EMPIRICALLY"})["verdict"] == C.REFUTED
    assert _judge(links, {"conservation": "UNKNOWN", "shock_speed": "REFUTED_EMPIRICALLY"})["verdict"] == C.REFUTED_EMPIRICALLY
    assert _judge(links, {"conservation": "VERIFIED", "shock_speed": "NOT_REFUTED"})["verdict"] == C.VERIFIED
    assert _judge(links, {"conservation": "UNKNOWN", "shock_speed": "NOT_REFUTED"})["verdict"] == C.NOT_REFUTED
    assert _judge(links, {})["verdict"] == C.UNKNOWN and "no check" in _judge(links, {})["detail"]


def test_contradictory_evidence_is_inconsistent_and_loud():
    """A deliberately contradictory fake check: conservation proved, and a 'necessary' check failing."""
    v = _judge([("conservation", C.EQUIVALENT), ("fake_contradiction", C.NECESSARY)],
               {"conservation": "VERIFIED", "fake_contradiction": "REFUTED"})
    assert v["verdict"] == C.INCONSISTENT and v["verdict"] in C.FAILURES
    assert set(v["decided_by"]) == {"conservation", "fake_contradiction"} and "bug" in v["detail"]
    out = render({"name": "fake"}, {"checks": [], "claims": [v]})
    assert "FAILS c" in out and "!!! [INCONSISTENT]" in out


def test_empirical_pass_never_verifies():
    """A misconfigured fake row: the empirical shock-speed study as EQUIVALENT. Its pass is evidence of
    "not refuted" polarity, so it gives NOT_REFUTED, never VERIFIED, and cannot by itself contradict a
    refutation. Its failure stays decisive, so against an exact pass it is still INCONSISTENT."""
    for status in ("NOT_REFUTED", "VERIFIED"):                  # even if the study claims an exact pass
        v = _judge([("shock_speed", C.EQUIVALENT)], {"shock_speed": status})
        assert v["verdict"] == C.NOT_REFUTED and v["evidence"][0]["polarity"] == "not_refuted"
        v = _judge([("shock_speed", C.EQUIVALENT), ("conservation", C.EQUIVALENT)],
                   {"shock_speed": status, "conservation": "REFUTED"})
        assert v["verdict"] == C.REFUTED and v["decided_by"] == ["conservation"]
        v = _judge([("shock_speed", C.EQUIVALENT), ("order/space", C.NECESSARY)],
                   {"shock_speed": status, "order/space": "REFUTED_EMPIRICALLY"})
        assert v["verdict"] == C.REFUTED_EMPIRICALLY and v["decided_by"] == ["order/space"]
    v = _judge([("conservation", C.EQUIVALENT), ("shock_speed", C.EQUIVALENT)],
               {"conservation": "VERIFIED", "shock_speed": "REFUTED_EMPIRICALLY"})
    assert v["verdict"] == C.INCONSISTENT and set(v["decided_by"]) == {"conservation", "shock_speed"}


def test_claims_table_is_well_formed():
    for statement, links in C.CLAIMS.values():
        assert statement and links
        for chk, rel, _, *requires in links:
            assert chk in C.GUARANTEE and rel in (C.SUFFICIENT, C.NECESSARY, C.EQUIVALENT)
            assert len(requires) <= 1 and all(C.GUARANTEE[r] == C.EXACT for r in (requires or [()])[0])
    with pytest.raises(ValueError):
        check({**load(S / "advection-upwind.json"), "named_claims": ["stable"]})


@pytest.mark.parametrize("name", CORRECT + sorted(BROKEN))
def test_claim_verdicts(verdicts, name):
    v = verdicts[name]
    assert v and not [c for c, x in v.items() if x["verdict"] == C.INCONSISTENT]
    assert {c: x["verdict"] for c, x in v.items() if x["verdict"] in C.FAILURES} == FAILING_CLAIMS.get(name, {})
    assert set(v) == set(load(S / f"{name}.json")["named_claims"])


def test_harten_is_not_refuted_by_tadmor(results, verdicts):
    """Tadmor's inequality is sufficient for the semi-discrete scheme selecting the entropy solution,
    not necessary: Harten's fix fails it (exactly, at (-1, 1)) and still converges to the rarefaction.
    It says nothing about time stepping, so it never decides the fully discrete claim: for Harten
    (not monotone either) the study alone does, for the monotone schemes monotonicity does."""
    assert results["burgers-roe-harten-fix"]["entropy_stability"]["status"] == checks.REFUTED
    harten = verdicts["burgers-roe-harten-fix"]
    v = harten["selects_entropy_solution"]
    assert v["verdict"] == C.NOT_REFUTED and v["guarantee"] == C.EMPIRICAL
    assert v["decided_by"] == ["entropy_rarefaction"]
    assert {e["check"]: e["gives"] for e in v["evidence"]} == {"entropy_rarefaction": C.NOT_REFUTED,
                                                                "steady_nonentropy_step": C.UNKNOWN}
    assert harten["selects_entropy_solution_semidiscrete"]["verdict"] == C.UNKNOWN
    roe = verdicts["broken-burgers-roe-no-entropy-fix"]
    assert roe["entropy_stable_tadmor"]["verdict"] == C.REFUTED and roe["entropy_stable_tadmor"]["guarantee"] == C.EXACT
    assert roe["selects_entropy_solution"]["decided_by"] == ["steady_nonentropy_step"]    # exact beats empirical
    assert roe["selects_entropy_solution_semidiscrete"]["verdict"] == C.UNKNOWN    # a failed sufficient condition
    for name in BURGERS:                                     # Tadmor VERIFIED decides it, with its premises
        v = verdicts[name]["selects_entropy_solution_semidiscrete"]
        assert v["verdict"] == C.VERIFIED and any("semi-discrete" in a for a in v["assumes"])
        v = verdicts[name]["selects_entropy_solution"]
        assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["monotonicity"]
        assert "entropy_stability" not in {e["check"] for e in v["evidence"]}


def test_conservation_claim_three_ways(verdicts):
    """The shock speed is only necessary for conservation: on the conservative schemes it adds nothing
    to the exact proof, and on the non-conservative one the exact refutation decides."""
    v = verdicts["broken-burgers-nonconservative"]["conservative"]
    assert v["verdict"] == C.REFUTED and v["decided_by"] == ["conservation"]
    assert verdicts["broken-burgers-nonconservative"]["converges_order_p"]["verdict"] == C.NOT_REFUTED
    for name in BURGERS:
        assert verdicts[name]["conservative"]["decided_by"] == ["conservation"]


# ---------------------------------------------------------------- monotonicity (fully discrete)

MONOTONE = {"advection-upwind": "1", "advection-lax-friedrichs": "1", "burgers-lax-friedrichs": "1",
            "burgers-engquist-osher": "1", "burgers-rusanov": "1/3", "broken-burgers-nonconservative": "1/3"}


def _with_cfl(name, c):
    spec = load(S / f"{name}.json")
    spec["claims"]["monotone_cfl"] = c
    return spec


def _in_region(spec, state, lam, c):
    """lam*|f'(u)| <= c on every state, recomputed from f' = a (advection) or f' = u (Burgers)."""
    a = Fraction(spec.get("params", {}).get("a", 0))
    return all(lam * abs(a if spec["pde"]["flux"] == "a*u" else u) <= c for u in state)


def test_derivative():
    assert P.add(P.derivative(_p("u^3*lam^-1 + 2*u*v + v"), "u"), _p("3*u^2/lam + 2*v"), -1) == {}
    with pytest.raises(P.Undecided):
        P.derivative(_p("sqrt(u^2)"), "u")


def test_monotone_specs_verified(results):
    for name, c in MONOTONE.items():
        r = results[name]["monotonicity"]
        assert r["status"] == checks.VERIFIED and r["guarantee"] == checks.EXACT, name
        assert f"<= {c}" in r["claim"]


@pytest.mark.parametrize("name", sorted(MONOTONE))
def test_monotone_certificates_hold(results, name):
    """Tests the checker: on exact random states in the CFL region, raising one argument never lowers H;
    and every Farkas identity recorded in the witness holds in the normal form."""
    spec, c = load(S / f"{name}.json"), Fraction(MONOTONE[name])
    H = P.from_expr(checks.update(spec))
    rng = random.Random(name)
    burgers = spec["pde"]["flux"] != "a*u"
    n = 0
    while n < 200:
        lam = Fraction(rng.randint(1, 9), rng.randint(1, 9)) if burgers else c * Fraction(rng.randint(1, 9), 9)
        scale = c / lam if burgers else 3                     # draw states inside the box (Burgers)
        s = [scale * Fraction(rng.randint(-60, 60), 60) for _ in range(3)]
        k, h = rng.randrange(3), scale * Fraction(rng.randint(1, 20), rng.randint(20, 400))
        t = s.copy()
        t[k] += h
        if not (_in_region(spec, s, lam, c) and _in_region(spec, t, lam, c)):
            continue
        at = lambda st: P.evaluate(H, {**dict(zip(checks.STENCIL, st)), "lam": lam})
        assert at(t) >= at(s), (s, t, lam)
        n += 1
    for cell in results[name]["monotonicity"]["witness"]["cells"]:
        for part in cell["partials"].values():
            cert = part["certificate"]
            if "farkas" in cert:
                lhs, rhs = cert["farkas"].split(" = ")
                assert P.add(_p(lhs), _p(rhs), -1) == {}
                assert all(Fraction(m) > 0 for m in cert["multipliers"].values()) and Fraction(cert["remainder"]) >= 0


def _replay_decrease(spec, r):
    """An exact REFUTED witness: two states in the region, one argument raised, H lower."""
    w = r["witness"]["counterexample"]
    c, lam = Fraction(spec["claims"]["monotone_cfl"]), Fraction(w["lam"])
    s = [Fraction(x) for x in w["state (um1, u0, up1)"]]
    t = s.copy()
    t[checks.STENCIL.index(w["increased"])] += Fraction(w["by"])
    assert Fraction(w["by"]) > 0 and lam > 0 and _in_region(spec, s, lam, c) and _in_region(spec, t, lam, c)
    H = P.from_expr(checks.update(spec))
    at = lambda st: P.evaluate(H, {**dict(zip(checks.STENCIL, st)), "lam": lam})
    assert at(t) == Fraction(w["H after"]) < Fraction(w["H before"]) == at(s)
    return lam, s, w["increased"]


@pytest.mark.parametrize("name,c", [("burgers-lax-friedrichs", "11/10"), ("burgers-lax-friedrichs", "101/100"),
                                    ("burgers-engquist-osher", "101/100"), ("advection-upwind", "11/10"),
                                    ("advection-lax-wendroff", "1"), ("broken-burgers-roe-no-entropy-fix", "1/10"),
                                    ("burgers-roe-harten-fix", "1/2"), ("broken-burgers-nonconservative", "334/1000")])
def test_monotonicity_refutations_replay(name, c):
    """The CFL ranges in the specs are sharp: just above them each scheme is exactly REFUTED (Rusanov's
    1/3 is tested in test_rusanov_monotone_bound_is_one_third)."""
    spec = _with_cfl(name, c)
    r = checks.monotonicity(spec)
    assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
    _replay_decrease(spec, r)


def _rusanov_h(um1, u0, up1, lam):
    """Rusanov for Burgers written independently of the spec, with alpha = max(|uL|, |uR|) taken literally."""
    F = lambda l, r: (l * l + r * r) / 4 - max(abs(l), abs(r)) * (r - l) / 2
    return u0 - lam * (F(u0, up1) - F(um1, u0))


def test_rusanov_monotone_bound_is_one_third(results):
    """Regression for a reported counterexample: Rusanov is not monotone under lam*max|u| <= 1. At lam = 9/10,
    raising u0 from 1 to 101/100 (lam*max|u| = 909/1000) lowers H from 751/4000 to 18011/100000, both in the
    spec's normal form and in an independent max() implementation. alpha = |u0| on the cell up1 < 0 < u0,
    |u0| >= |up1|, so dF/duL gains -(up1 - u0)/2. The bound is 1/3, sharper than 1/2: 1/2 is refuted too.
    The checker must never verify above 1/3, and every refutation must replay in the independent H."""
    H = P.from_expr(checks.update(load(S / "burgers-rusanov.json")))
    at = lambda *s: P.evaluate(H, dict(zip(("um1", "u0", "up1", "lam"), s)))
    one = Fraction(1)
    lam, a, b = Fraction(9, 10), (one, one, Fraction(-9, 10)), (one, Fraction(101, 100), Fraction(-9, 10))
    assert at(*a, lam) == _rusanov_h(*a, lam) == Fraction(751, 4000)
    assert at(*b, lam) == _rusanov_h(*b, lam) == Fraction(18011, 100000)
    assert lam * Fraction(101, 100) <= 1
    assert results["broken-burgers-rusanov-wide-cfl"]["monotonicity"]["status"] == checks.REFUTED
    assert results["burgers-rusanov"]["monotonicity"]["status"] == checks.VERIFIED
    for c in ("1", "1/2", "334/1000"):                       # Rusanov's refutations live here, once each
        r = (results["broken-burgers-rusanov-wide-cfl"]["monotonicity"] if c == "1" else
             checks.monotonicity(_with_cfl("burgers-rusanov", c)))
        assert r["status"] == checks.REFUTED, c
        w = r["witness"]["counterexample"]
        lam, s = Fraction(w["lam"]), [Fraction(x) for x in w["state (um1, u0, up1)"]]
        t = s.copy()
        t[checks.STENCIL.index(w["increased"])] += Fraction(w["by"])
        assert lam * max(map(abs, s + t)) <= Fraction(c) and _rusanov_h(*t, lam) < _rusanov_h(*s, lam)
    rng = random.Random(9)                                   # at 1/3 the independent H never decreases
    for _ in range(400):
        lam = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        s = [Fraction(rng.randint(-90, 90), 270) / lam for _ in range(3)]
        k, t = rng.randrange(3), s.copy()
        t[k] = min(t[k] + Fraction(rng.randint(1, 30), 270) / lam, Fraction(1, 3) / lam)
        assert _rusanov_h(*t, lam) >= _rusanov_h(*s, lam)


def test_lax_wendroff_is_not_monotone(results):
    """Godunov: a linear monotone scheme is at most first order. Lax-Wendroff is REFUTED for every
    lam in (0, 1): the coefficient of up1 is -lam*(1 - lam)/2 < 0. At lam = 1 it is the exact shift."""
    r = results["broken-advection-lax-wendroff-monotone"]["monotonicity"]
    lam, _, x = _replay_decrease(load(S / "broken-advection-lax-wendroff-monotone.json"), r)
    assert 0 < lam < 1 and x == "up1"
    assert r["witness"]["cells"][0]["partials"]["up1"]["dH/dup1"] == "-1/2*lam + 1/2*lam^2"


def test_roe_is_not_monotone_at_a_transonic_expansion(results):
    """Roe without a fix is not monotone under any CFL bound: near the expansion um1 < 0 < u0 the flux is
    uL^2/2, so dH/dum1 = lam*um1 < 0. Monotonicity is only sufficient, so this alone decides nothing
    about the entropy claim; the rarefaction study refutes it, with no INCONSISTENT."""
    r = results["broken-burgers-roe-no-entropy-fix"]["monotonicity"]
    lam, s, x = _replay_decrease(load(S / "broken-burgers-roe-no-entropy-fix.json"), r)
    assert x == "um1" and s[0] < 0 < s[1]


def test_monotone_and_positive_agree_on_linear_schemes():
    """For a linear update, monotone on lam*|a| <= c is positivity on nu in [0, c] (a = 1)."""
    for name in ("advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff", "broken-advection-downwind"):
        for c in ("1/2", "1", "11/10"):
            spec = _with_cfl(name, c)
            spec["claims"]["positive_cfl"] = ["0", c]
            assert checks.monotonicity(spec)["status"] == checks.positivity(spec)["status"], (name, c)


def test_crandall_majda_needs_conservation_and_consistency(verdicts):
    """A monotone, non-conservative update must not verify the entropy claim: the row's precondition."""
    v = verdicts["broken-burgers-nonconservative"]
    assert v["monotone_under_cfl"]["verdict"] == C.VERIFIED
    s = v["selects_entropy_solution"]
    assert s["verdict"] == C.UNKNOWN and next(e for e in s["evidence"] if e["check"] == "monotonicity")["unmet"] == ["conservation: REFUTED", "consistency: NOT_APPLICABLE"]
    row = next(r for r in C.CLAIMS["selects_entropy_solution"][1] if r[0] == "monotonicity")
    table = {"c": ("test claim", (row,))}
    judge = lambda st: C.judge(["c"], [{"check": k, "status": x, "assumptions": []} for k, x in st.items()], table)[0]
    ok = {"monotonicity": "VERIFIED", "conservation": "VERIFIED", "consistency": "VERIFIED"}
    assert judge(ok)["verdict"] == C.VERIFIED and "Crandall-Majda" in judge(ok)["assumes"][0]
    for k, bad in (("conservation", "REFUTED"), ("consistency", "UNKNOWN"), ("consistency", None)):
        st = {**ok, k: bad} if bad else {x: y for x, y in ok.items() if x != k}
        assert judge(st)["verdict"] == C.UNKNOWN, (k, bad)
    # if a monotone, conservative, consistent scheme kept an expansion shock, the judge would say so loudly
    links = C.CLAIMS["selects_entropy_solution"][1]
    loud = C.judge(["c"], [{"check": k, "status": x, "assumptions": []} for k, x in
                           {**ok, "entropy_rarefaction": "REFUTED_EMPIRICALLY"}.items()], {"c": ("t", links)})[0]
    assert loud["verdict"] == C.INCONSISTENT


# ---------------------------------------------------------------- exact order (linear schemes)

LINEAR = ["advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff",
          "broken-advection-fake-second-order", "broken-advection-ftcs"]


def _unit_coefficients(spec, nu):
    """c_{-1}, c_0, c_1 at nu, read off the spec's update expression at unit stencil vectors (independent
    of the coefficient extraction the checks use)."""
    H, a = P.from_expr(checks.update(spec)), Fraction(spec["params"]["a"])
    unit = lambda name: {**{s: Fraction(0) for s in checks.STENCIL}, name: Fraction(1), "lam": nu / a}
    return [P.evaluate(H, unit(s)) for s in checks.STENCIL]


def _g2(spec, nu, z):
    """|g|^2 = (c_0 + (c_1 + c_-1) z)^2 + (c_1 - c_-1)^2 (1 - z^2), from Re g and Im g with cos(theta) = z."""
    cm, c0, cp = _unit_coefficients(spec, nu)
    return (c0 + (cp + cm) * z) ** 2 + (cp - cm) ** 2 * (1 - z * z)


@pytest.mark.parametrize("name", LINEAR)
def test_truncation_terms_replay_on_monomials(name):
    """e_q is the truncation error on u = (x - a t)^q at x = 0, dx = 1, divided by q!: recompute it from the
    spec's update evaluated at the stencil values of x^q."""
    spec = load(S / f"{name}.json")
    a, c = linear.coefficients(spec, "t", "t")[0]
    e = linear.truncation_terms(a, c, 5)
    H = P.from_expr(checks.update(spec))
    for nu in (Fraction(1, 2), Fraction(-2, 3), Fraction(7, 5)):
        lam = nu / a
        for q in range(6):
            stencil = {s: Fraction(k) ** q for s, k in zip(checks.STENCIL, (-1, 0, 1))}
            tau = ((-a * lam) ** q - P.evaluate(H, {**stencil, "lam": lam})) / lam
            assert tau / factorial(q) == P.evaluate(e[q], {"nu": nu}), (name, nu, q)


def test_truncation_orders_and_leading_terms(results):
    want = {"advection-upwind": (checks.VERIFIED, 1, "diffusive"), "advection-lax-friedrichs": (checks.VERIFIED, 1, "diffusive"),
            "advection-lax-wendroff": (checks.VERIFIED, 2, "dispersive"),
            "broken-advection-fake-second-order": (checks.REFUTED, 1, "anti-diffusive"),
            "broken-advection-ftcs": (checks.VERIFIED, 1, "anti-diffusive")}
    for name, (status, order, kind) in want.items():
        r = results[name]["truncation_order"]
        assert (r["status"], r["witness"]["order"]) == (status, order), name
        assert r["witness"]["leading_term"]["kind"].startswith(kind), name
    lw = results["advection-lax-wendroff"]["truncation_order"]["witness"]
    assert P.add(_p(lw["leading_term"]["e_j"]), _p("(1 - nu^2)/6"), -1) == {}       # u_t + a u_x = -a dx^2 (1 - nu^2)/6 u_xxx
    up = results["advection-upwind"]["truncation_order"]["witness"]
    assert P.add(_p(up["leading_term"]["e_j"]), _p("(nu - 1)/2"), -1) == {}         # diffusion a dx (1 - nu)/2
    fake = results["broken-advection-fake-second-order"]["truncation_order"]["witness"]
    assert fake["offending_j"] == 2 and Fraction(fake["e_j_value"]) == Fraction(fake["nu_value"]) / 4 != 0
    # Lax-Wendroff claimed only first order: VERIFIED, and the extra order is reported, not a failure
    spec = load(S / "advection-lax-wendroff.json")
    spec["claims"]["consistent_order"] = 1
    r = linear.truncation_order(spec)
    assert r["status"] == checks.VERIFIED and "higher than claimed" in r["detail"]
    spec["claims"]["consistent_order"] = 3
    r = linear.truncation_order(spec)
    assert r["status"] == checks.REFUTED and r["witness"]["offending_j"] == 3


def test_tensor_bernstein():
    unit = (Fraction(0), Fraction(1))
    assert linear.tensor_bernstein([[0, 0], [0, 1]], unit, unit) == [[0, 0], [0, 1]]       # nu*z
    b = linear.tensor_bernstein([[Fraction(1), Fraction(-1)]], (Fraction(0), Fraction(2)), (Fraction(-1), Fraction(1)))
    assert b == [[1, -1]]                                   # 1 - nu on [0, 2]: endpoint values


def _von_neumann(name, lo, hi):
    spec = load(S / f"{name}.json")
    spec["claims"]["von_neumann_cfl"] = [lo, hi]
    return spec, linear.von_neumann(spec)


VN_STABLE = [("advection-upwind", "0", "1"), ("advection-lax-friedrichs", "-1", "1"), ("advection-lax-wendroff", "-1", "1")]
VN_UNSTABLE = [("advection-upwind", "0", "101/100"), ("advection-upwind", "-1/100", "1"),
               ("advection-lax-friedrichs", "0", "11/10"), ("advection-lax-friedrichs", "-101/100", "0"),
               ("advection-lax-wendroff", "0", "101/100"), ("broken-advection-ftcs", "1/1000", "1/1000"),
               ("broken-advection-ftcs", "-1/2", "-1/4"), ("broken-advection-fake-second-order", "1/1000", "1/1000")]


def test_von_neumann_certificates_hold():
    """Each VERIFIED range: the certificate's boxes cover it, and |g|^2 <= 1 at random exact (nu, z)."""
    rng = random.Random(4)
    for name, lo, hi in VN_STABLE:
        spec, r = _von_neumann(name, lo, hi)
        assert r["status"] == checks.VERIFIED, name
        boxes = r["witness"]["certificate"]["boxes"]
        area = sum((Fraction(b["nu"][1]) - Fraction(b["nu"][0])) * (Fraction(b["z"][1]) - Fraction(b["z"][0])) for b in boxes)
        assert area == (Fraction(hi) - Fraction(lo)) * 2
        assert all(Fraction(x) >= 0 for b in boxes for row in b["bernstein"] for x in row)
        for _ in range(200):
            nu = Fraction(lo) + (Fraction(hi) - Fraction(lo)) * Fraction(rng.randint(0, 997), 997)
            z = Fraction(rng.randint(-991, 991), 991)
            assert _g2(spec, nu, z) <= 1, (name, nu, z)


@pytest.mark.parametrize("name,lo,hi", VN_UNSTABLE)
def test_von_neumann_refutations_replay(name, lo, hi):
    """Just outside each stable range, and anywhere for FTCS and the halved Lax-Wendroff: an exact (nu, z)
    in the range with |g|^2 > 1, recomputed from Re g and Im g."""
    spec, r = _von_neumann(name, lo, hi)
    assert r["status"] == checks.REFUTED
    w = r["witness"]["counterexample"]
    nu, z = Fraction(w["nu"]), Fraction(w["z = cos(theta)"])
    assert Fraction(lo) <= nu <= Fraction(hi) and -1 <= z <= 1
    assert _g2(spec, nu, z) == Fraction(w["|g|^2"]) > 1


def test_lax_wide_cfl_and_ftcs_witnesses(results):
    w = results["broken-advection-lax-friedrichs-wide-cfl"]["von_neumann"]["witness"]["counterexample"]
    assert (w["nu"], w["z = cos(theta)"], w["|g|^2"]) == ("11/10", "0", "121/100")    # |g|^2 = z^2 + nu^2 (1 - z^2)
    G = _p(results["broken-advection-ftcs"]["von_neumann"]["witness"]["1 - |g|^2"])
    assert P.add(G, _p("-nu^2*(1 - z^2)"), -1) == {}                                   # < 0 for every nu != 0, |z| < 1


def test_lax_richtmyer_row(verdicts, results):
    """Consistent of order p + von Neumann stable + in scope: converges_order_p VERIFIED (exact, Lax-Richtmyer)."""
    for name in ("advection-lax-friedrichs", "advection-lax-wendroff"):
        v = verdicts[name]["converges_order_p"]
        assert v["verdict"] == C.VERIFIED and v["guarantee"] == C.EXACT and v["decided_by"] == ["truncation_order"]
        assert any("Lax-Richtmyer" in a and "error constant" in a for a in v["assumes"])
        assert {e["check"]: e["gives"] for e in v["evidence"]}["order/combined"] == C.NOT_REFUTED   # the study agrees
    # upwind also claims space and time studies, which the theorem (fixed dt/dx) does not cover
    assert verdicts["advection-upwind"]["converges_order_p"]["verdict"] == C.NOT_REFUTED
    scope = results["advection-upwind"]["lax_richtmyer_scope"]
    assert scope["status"] == checks.NOT_APPLICABLE and "combined" in scope["detail"]
    # FTCS: consistent, but unstable, so the row says nothing and the blown-up study decides
    ftcs = verdicts["broken-advection-ftcs"]
    assert ftcs["consistent_order_p"]["verdict"] == C.VERIFIED
    row = next(e for e in ftcs["converges_order_p"]["evidence"] if e["check"] == "truncation_order")
    assert row["gives"] == C.UNKNOWN and row["unmet"] == ["von_neumann: REFUTED"]
    # halved Lax-Wendroff: the order-2 consistency claim fails, and a failed sufficient condition proves nothing
    assert verdicts["broken-advection-fake-second-order"]["converges_order_p"]["decided_by"] == ["order/combined"]
    links = C.CLAIMS["converges_order_p"][1]
    judge = lambda st: C.judge(["c"], [{"check": k, "status": x, "assumptions": []} for k, x in st.items()],
                               {"c": ("t", links)})[0]
    ok = {"truncation_order": "VERIFIED", "von_neumann": "VERIFIED", "lax_richtmyer_scope": "VERIFIED"}
    assert judge(ok)["verdict"] == C.VERIFIED
    for k, bad in (("von_neumann", "UNKNOWN"), ("lax_richtmyer_scope", "NOT_APPLICABLE"), ("von_neumann", None)):
        st = {**ok, k: bad} if bad else {x: y for x, y in ok.items() if x != k}
        assert judge(st)["verdict"] == C.UNKNOWN, (k, bad)
    assert judge({**ok, "order/combined": "REFUTED_EMPIRICALLY"})["verdict"] == C.INCONSISTENT    # loud, if it ever happened


def test_lax_richtmyer_never_fires_for_nonlinear_schemes():
    """Burgers Lax-Friedrichs with every precondition claimed: the update is not linear, so all three new
    checks are NOT_APPLICABLE and converges_order_p stays with the study."""
    spec = load(S / "burgers-lax-friedrichs.json")
    spec["named_claims"] = ["consistent_order_p", "von_neumann_stable_under_cfl", "converges_order_p"]
    spec["claims"] = {"order": {"combined": 1}, "consistent_order": 1, "von_neumann_cfl": ["0", "1"]}
    rep = check(spec)
    st = {r["check"]: r["status"] for r in rep["checks"]}
    assert {st[k] for k in ("truncation_order", "von_neumann", "lax_richtmyer_scope")} == {checks.NOT_APPLICABLE}
    v = {x["claim"]: x["verdict"] for x in rep["claims"]}
    assert v == {"consistent_order_p": C.UNKNOWN, "von_neumann_stable_under_cfl": C.UNKNOWN,
                 "converges_order_p": C.NOT_REFUTED}


def test_ftcs_study_can_miss_the_instability():
    """At dt/dx = 1/2 to T = 1/4 the round-off has not grown enough by N = 400 and the study sees order 1.
    The exact von Neumann check refutes stability; the judge says NOT_REFUTED, never VERIFIED or INCONSISTENT."""
    spec = load(S / "broken-advection-ftcs.json")
    spec["test"] = {**spec["test"], "lam": 0.5, "T": 0.25}
    rep = check(spec)
    st = {r["check"]: r["status"] for r in rep["checks"]}
    assert st["order/combined"] == convergence.NOT_REFUTED and st["von_neumann"] == checks.REFUTED
    v = {x["claim"]: x["verdict"] for x in rep["claims"]}
    assert v["converges_order_p"] == C.NOT_REFUTED and v["von_neumann_stable_under_cfl"] == C.REFUTED
