"""Tests for the discrete-scheme checker (physverify/schemes)."""
import random
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from physverify.expr import parse
from physverify.schemes import FAILURES, check, checks, convergence, load, poly as P

S = Path(__file__).resolve().parent.parent / "schemes"
CORRECT = ["advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff",
           "burgers-lax-friedrichs", "burgers-engquist-osher", "burgers-rusanov"]
# broken spec -> the checks that must catch it (and nothing else may fail)
BROKEN = {"broken-advection-inconsistent-flux": {"consistency", "order/combined"},
          "broken-burgers-scaled-flux": {"consistency", "order/combined"},
          "broken-burgers-nonconservative": {"conservation"},
          "broken-advection-lax-friedrichs-wide-cfl": {"positivity"},
          "broken-advection-downwind": {"positivity"},
          "broken-advection-fake-second-order": {"order/combined"}}


def _p(s):
    return P.from_expr(parse(s))


@pytest.fixture(scope="module")
def results():
    return {name: {r["check"]: r for r in check(load(S / f"{name}.json"))} for name in CORRECT + list(BROKEN)}


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
