"""Tests for the discrete-scheme checker (physverify/schemes)."""
import random
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from physverify.expr import parse
from physverify.schemes import FAILURES, check, checks, claims as C, convergence, entropy, load, poly as P, render, shock

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
          "broken-burgers-roe-no-entropy-fix": {"entropy_stability", "entropy_rarefaction"},
          "broken-advection-lax-friedrichs-wide-cfl": {"positivity"},
          "broken-advection-downwind": {"positivity"},
          "broken-advection-fake-second-order": {"order/combined"}}


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
                                                        "selects_entropy_solution": C.REFUTED_EMPIRICALLY},
                  "broken-advection-lax-friedrichs-wide-cfl": {"positive_under_cfl": C.REFUTED},
                  "broken-advection-downwind": {"positive_under_cfl": C.REFUTED},
                  "broken-advection-fake-second-order": {"converges_order_p": C.REFUTED_EMPIRICALLY}}

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


def test_claims_table_is_well_formed():
    for statement, links in C.CLAIMS.values():
        assert statement and links
        for chk, rel, _ in links:
            assert chk in C.GUARANTEE and rel in (C.SUFFICIENT, C.NECESSARY, C.EQUIVALENT)
    with pytest.raises(ValueError):
        check({**load(S / "advection-upwind.json"), "named_claims": ["stable"]})


@pytest.mark.parametrize("name", CORRECT + sorted(BROKEN))
def test_claim_verdicts(verdicts, name):
    v = verdicts[name]
    assert v and not [c for c, x in v.items() if x["verdict"] == C.INCONSISTENT]
    assert {c: x["verdict"] for c, x in v.items() if x["verdict"] in C.FAILURES} == FAILING_CLAIMS.get(name, {})
    assert set(v) == set(load(S / f"{name}.json")["named_claims"])


def test_harten_is_not_refuted_by_tadmor(results, verdicts):
    """Tadmor's inequality is sufficient for selecting the entropy solution, not necessary: Harten's
    fix fails it (exactly, at (-1, 1)) and still converges to the rarefaction."""
    assert results["burgers-roe-harten-fix"]["entropy_stability"]["status"] == checks.REFUTED
    v = verdicts["burgers-roe-harten-fix"]["selects_entropy_solution"]
    assert v["verdict"] == C.NOT_REFUTED and v["guarantee"] == C.EMPIRICAL
    assert v["decided_by"] == ["entropy_rarefaction"]
    assert {e["check"]: e["gives"] for e in v["evidence"]} == {"entropy_stability": C.UNKNOWN,
                                                               "entropy_rarefaction": C.NOT_REFUTED}
    roe = verdicts["broken-burgers-roe-no-entropy-fix"]
    assert roe["entropy_stable_tadmor"]["guarantee"] == C.EXACT
    assert roe["selects_entropy_solution"]["decided_by"] == ["entropy_rarefaction"]
    for name in BURGERS:                                     # Tadmor VERIFIED decides it, with its premises
        v = verdicts[name]["selects_entropy_solution"]
        assert v["verdict"] == C.VERIFIED and any("semi-discrete" in a for a in v["assumes"])


def test_conservation_claim_three_ways(verdicts):
    """The shock speed is only necessary for conservation: on the conservative schemes it adds nothing
    to the exact proof, and on the non-conservative one the exact refutation decides."""
    v = verdicts["broken-burgers-nonconservative"]["conservative"]
    assert v["verdict"] == C.REFUTED and v["decided_by"] == ["conservation"]
    assert verdicts["broken-burgers-nonconservative"]["converges_order_p"]["verdict"] == C.NOT_REFUTED
    for name in BURGERS:
        assert verdicts[name]["conservative"]["decided_by"] == ["conservation"]
