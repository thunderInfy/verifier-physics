"""Tests for the discrete-scheme checker (physverify/schemes)."""
import random
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from physverify.expr import parse
from physverify.schemes import FAILURES, check, checks, convergence, load, poly as P, shock

S = Path(__file__).resolve().parent.parent / "schemes"
BURGERS = ["burgers-lax-friedrichs", "burgers-engquist-osher", "burgers-rusanov"]
SHOCK_GRIDS = (100, 200, 400, 800)  # the CLI refines to N = 3200
CORRECT = ["advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff",
           "burgers-lax-friedrichs", "burgers-engquist-osher", "burgers-rusanov"]
# broken spec -> the checks that must catch it (and nothing else may fail)
BROKEN = {"broken-advection-inconsistent-flux": {"consistency", "order/combined"},
          "broken-burgers-scaled-flux": {"consistency", "order/combined"},
          "broken-burgers-nonconservative": {"conservation", "shock_speed"},
          "broken-advection-lax-friedrichs-wide-cfl": {"positivity"},
          "broken-advection-downwind": {"positivity"},
          "broken-advection-fake-second-order": {"order/combined"}}


def _p(s):
    return P.from_expr(parse(s))


@pytest.fixture(scope="module")
def results():
    return {name: {r["check"]: r for r in check(load(S / f"{name}.json"), SHOCK_GRIDS)}
            for name in CORRECT + list(BROKEN)}


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
    if name in BURGERS:
        assert r["shock_speed"]["status"] == convergence.NOT_REFUTED


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
