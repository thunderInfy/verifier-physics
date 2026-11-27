"""Tests for the semi-discrete steady non-entropy step (checks.steady_nonentropy_step, mode
"semidiscrete") and for stability at every small CFL number (linear.von_neumann_small_cfl), with
their rows in the claims table."""
import cmath
import math
from fractions import Fraction
from pathlib import Path

import pytest

from physverify.schemes import check, checks, claims as C, linear, load, poly as P

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes"
B = ROOT / "benchmark" / "scheme-claims" / "specs"
SPECS = sorted(S.glob("*.json")) + sorted(B.glob("*.json"))
TADMOR_OK = ["burgers-engquist-osher", "burgers-lax-friedrichs", "burgers-rusanov"]
LAMS = [Fraction(2, 5), Fraction(1), Fraction(3)]


def _spec(name):
    return load(S / f"{name}.json")


def _claims(checked, spec, names):
    return {v["claim"]: v for v in checked({**spec, "named_claims": names}, (100, 200), (200, 400))["claims"]}


# ---------------------------------------------------------------- Part A: semi-discrete steady step

def _rhs(F, u, dx=Fraction(1, 10)):
    """-(F_{i+1/2} - F_{i-1/2})/dx on a finite grid with constant (transmissive) ghost cells, exactly."""
    g = [u[0]] + u + [u[-1]]
    flux = lambda a, b: P.evaluate(F, {"uL": a, "uR": b})
    return [-(flux(g[i], g[i + 1]) - flux(g[i - 1], g[i])) / dx for i in range(1, len(u) + 1)]


def test_roe_semidiscrete_step_is_exact_and_replays():
    spec = _spec("broken-burgers-roe-no-entropy-fix")
    r = checks.steady_nonentropy_step_semidiscrete(spec)
    assert r["check"] == "steady_nonentropy_step_semidiscrete"
    assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
    w = r["witness"]
    uL, uR = Fraction(w["uL"]), Fraction(w["uR"])
    assert (uL, uR) == (-1, 1) and w["found_by"] == "candidate pair" and w["identities"]["F(uL, uR)"] == "1/2"
    F = P.from_expr(checks.numerical_flux(spec))
    assert P.evaluate(F, {"uL": uL, "uR": uL}) == P.evaluate(F, {"uL": uL, "uR": uR}) == P.evaluate(F, {"uL": uR, "uR": uR})
    assert _rhs(F, [uL] * 4 + [uR] * 4) == [0] * 8                 # the step is a steady state of the ODE system
    assert Fraction(w["f'(uL)"]) < Fraction(w["f'(uR)"])
    assert any("expansion-shock weak solution" in a for a in r["assumptions"])


def test_roe_semidiscrete_claim_refuted_exactly(checked):
    v = _claims(checked, _spec("broken-burgers-roe-no-entropy-fix"), ["selects_entropy_solution_semidiscrete"])
    s = v["selects_entropy_solution_semidiscrete"]
    assert s["verdict"] == C.REFUTED and s["guarantee"] == C.EXACT
    assert s["decided_by"] == ["steady_nonentropy_step_semidiscrete"]
    assert {e["check"]: e["gives"] for e in s["evidence"]} == {"entropy_stability": C.UNKNOWN,
                                                                "steady_nonentropy_step_semidiscrete": C.REFUTED}
    assert any("method of lines" in a for a in s["assumes"])


@pytest.mark.parametrize("path", SPECS, ids=lambda p: p.stem)
def test_tadmor_verified_flux_has_no_steady_step(path, checked):
    """Cross-check of two exact checks. For a consistent flux, a steady step has F = f(uL) = f(uR), so
    [psi] = F [v] - [q], F - F* = [q]/[v] and Tadmor's Q = -[q]. For uL < uR with convex f the step is an
    expansion shock, which violates the entropy inequality for a strictly convex entropy: [q] > 0, so
    Q < 0 and Tadmor's check cannot verify. So the step check must never refute a Tadmor-VERIFIED flux,
    and the judge must never say INCONSISTENT."""
    spec = load(path)
    t = checks.entropy_stability({**spec, "claims": {"entropy_stability": {}, **spec.get("claims", {})}})
    st = checks.steady_nonentropy_step_semidiscrete(spec)
    if t["status"] == checks.VERIFIED:
        assert st["status"] != checks.REFUTED
    if checks.numerical_flux(spec) is not None and "u^2" in spec["pde"]["flux"]:
        v = _claims(checked, spec, ["selects_entropy_solution_semidiscrete"])["selects_entropy_solution_semidiscrete"]
        assert v["verdict"] != C.INCONSISTENT


def test_tadmor_verified_specs_on_disk(checked):
    """The cross-check above has real cases: the three monotone Burgers fluxes (and the benchmark's
    variants) are Tadmor-VERIFIED, and the step check finds nothing, so they stay VERIFIED."""
    for name in TADMOR_OK:
        st = checks.steady_nonentropy_step_semidiscrete(_spec(name))
        assert st["status"] == checks.UNKNOWN and "proves nothing" in st["detail"] and "0 not decided" in st["detail"]
        v = _claims(checked, _spec(name), ["selects_entropy_solution_semidiscrete"])["selects_entropy_solution_semidiscrete"]
        assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["entropy_stability"]


def test_harten_fix_and_lax_friedrichs_viscosity_break_the_semidiscrete_step():
    harten = _spec("burgers-roe-harten-fix")
    assert checks.steady_nonentropy_step_semidiscrete(harten)["status"] == checks.UNKNOWN
    F = P.from_expr(checks.numerical_flux(harten))
    res = checks.semidiscrete_identities(F, Fraction(-1), Fraction(1))
    assert all(res.values())                                      # the fix's viscosity at the sonic interface
    lf = P.from_expr(checks.numerical_flux(_spec("burgers-lax-friedrichs")))
    res = checks.semidiscrete_identities(lf, Fraction(-1), Fraction(1))
    assert {k: P.show(v) for k, v in res.items()} == {"F(uL, uR) - F(uL, uL)": "-lam^-1",
                                                       "F(uR, uR) - F(uL, uR)": "lam^-1"}


def test_semidiscrete_needs_no_consistency_and_labels_the_search(checked):
    """An inconsistent flux (F(u, u) = f(u) + 1) whose interface fluxes are equal on a step: refuted
    without a consistency precondition. A flux steady only at (-1/3, 3/2): found by the labelled search."""
    spec = {"name": "inconsistent", "pde": {"flux": "u^2/2"},
            "scheme": {"numerical_flux": "(uL^2 + uR^2)/4 + 1 - (uR - uL)*(uL + uR)/4"}, "claims": {}}
    # F = uL^2/2 + 1: F(uL, uR) = F(uL, uL), and = F(uR, uR) iff uL^2 = uR^2
    assert checks.consistency(spec)["status"] == checks.REFUTED
    r = checks.steady_nonentropy_step_semidiscrete(spec)
    assert r["status"] == checks.REFUTED and (r["witness"]["uL"], r["witness"]["uR"]) == ("-1", "1")
    assert _claims(checked, spec, ["selects_entropy_solution_semidiscrete"])["selects_entropy_solution_semidiscrete"][
        "verdict"] == C.REFUTED
    off = {**spec, "scheme": {"numerical_flux": "uL^2/2 + (uR - uL)*(uL + 1/3)*(uR - 3/2)*(uR - uL - 11/6)"}}
    # F(u, u) = f(u); F(uL, uR) = f(uL) needs uL = -1/3 or uR = 3/2 or uR - uL = 11/6, and f(uL) = f(uR) needs uR = -uL
    w = checks.steady_nonentropy_step_semidiscrete(off)["witness"]
    assert w["found_by"] == "search over small rationals"
    uL, uR = Fraction(w["uL"]), Fraction(w["uR"])
    F = P.from_expr(checks.numerical_flux(off))
    assert P.evaluate(F, {"uL": uL, "uR": uL}) == P.evaluate(F, {"uL": uL, "uR": uR}) == P.evaluate(F, {"uL": uR, "uR": uR})


def test_semidiscrete_out_of_scope():
    assert checks.steady_nonentropy_step_semidiscrete(_spec("advection-upwind"))["status"] == checks.NOT_APPLICABLE
    upd = _spec("broken-burgers-nonconservative")            # an update, no numerical flux
    r = checks.steady_nonentropy_step_semidiscrete(upd)
    assert r["status"] == checks.NOT_APPLICABLE and "no numerical flux" in r["detail"]


def test_both_instantiations_share_one_implementation():
    spec = _spec("broken-burgers-roe-no-entropy-fix")
    d, s = checks.steady_nonentropy_step(spec), checks.steady_nonentropy_step(spec, "semidiscrete")
    assert d["check"] == "steady_nonentropy_step" and s == checks.steady_nonentropy_step_semidiscrete(spec)
    assert (d["witness"]["uL"], d["witness"]["uR"]) == (s["witness"]["uL"], s["witness"]["uR"])
    for lam in LAMS:                                         # discrete identities still replay
        H = P.from_expr(checks.update(spec))
        assert P.evaluate(H, {"um1": -1, "u0": -1, "up1": 1, "lam": lam}) == -1


def test_semidiscrete_row():
    rows = {r[0]: r for r in C.CLAIMS["selects_entropy_solution_semidiscrete"][1]}
    row = rows["steady_nonentropy_step_semidiscrete"]
    assert row[1] == C.NECESSARY and len(row) == 3 and C.GUARANTEE[row[0]] == C.EXACT
    assert rows["entropy_stability"][1] == C.SUFFICIENT
    table = {"c": ("t", C.CLAIMS["selects_entropy_solution_semidiscrete"][1])}
    judge = lambda st: C.judge(["c"], [{"check": k, "status": x, "assumptions": []} for k, x in st.items()], table)[0]
    assert judge({"steady_nonentropy_step_semidiscrete": "REFUTED"})["verdict"] == C.REFUTED
    assert judge({"steady_nonentropy_step_semidiscrete": "UNKNOWN"})["verdict"] == C.UNKNOWN
    # Tadmor VERIFIED together with a steady step would be a checker bug, reported loudly
    assert judge({"entropy_stability": "VERIFIED",
                  "steady_nonentropy_step_semidiscrete": "REFUTED"})["verdict"] == C.INCONSISTENT


# ---------------------------------------------------------------- Part B: stability for small CFL

def _g2(spec, nu, theta):
    """|g|^2 straight from the update, in floating point: an independent replay of the witness."""
    _, c = checks.linear_coefficients(spec)
    g = sum(P.evaluate(p, {"nu": nu}) * cmath.exp(1j * linear.OFFSET[k] * theta) for k, p in c.items())
    return abs(g) ** 2


@pytest.mark.parametrize("path", [S / "broken-advection-ftcs.json", B / "advection-ftcs.json"], ids=lambda p: p.stem)
def test_ftcs_refuted_with_checkable_witness(path):
    spec = load(path)
    r = linear.von_neumann_small_cfl(spec)
    assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
    w = r["witness"]
    assert w["1 - |g|^2"] == "nu^2*z^2 - nu^2"                       # -nu^2 (1 - z^2)
    ref = w["refutation"]
    assert ref["k (lowest power of nu)"] == 2 and ref["q_k(z)"] == "z^2 - 1"
    assert ref["z0 = cos(theta)"] == "0" and ref["q_k(z0)"] == "-1" and ref["nu1"] == "1"
    for nu, val in ref["G(nu, z0) at nu"].items():                 # spot values: exact, and replayed from g
        nu, val = Fraction(nu), Fraction(val)
        assert 0 < nu <= 1 and val == -nu ** 2 < 0
        assert math.isclose(_g2(spec, nu, math.pi / 2), 1 - float(val), rel_tol=1e-12)
    assert any("max-norm" in a for a in r["assumptions"])


def test_refutation_bound_holds_on_a_grid():
    """The explicit nu1 is rigorous; check it densely on a scheme with higher-order terms (halved Lax-Wendroff
    diffusion: G = nu^2 (z^2 - z) + ...)."""
    spec = _spec("broken-advection-fake-second-order")
    ref = linear.von_neumann_small_cfl(spec)["witness"]["refutation"]
    z0, nu1, qk = Fraction(ref["z0 = cos(theta)"]), Fraction(ref["nu1"]), Fraction(ref["q_k(z0)"])
    k = ref["k (lowest power of nu)"]
    G = P.add(P.const(1), linear.amplification_squared(linear.coefficients(spec, "x", "x")[0][1]), -1)
    for j in range(1, 101):
        nu = nu1 * Fraction(j, 100)
        assert P.evaluate(G, {"nu": nu, "z": z0}) <= qk * nu ** k / 2 < 0


@pytest.mark.parametrize("name", ["advection-upwind", "advection-lax-friedrichs", "advection-lax-wendroff"])
def test_stable_schemes_verified(name, checked):
    spec = _spec(name)
    r = linear.von_neumann_small_cfl(spec)
    assert r["status"] == checks.VERIFIED and r["witness"]["nu0"] == "1"
    cert = r["witness"]["certificate"]
    assert all(Fraction(x) >= 0 for b in cert["boxes"] for row in b["bernstein"] for x in row)
    assert min(Fraction(b["nu"][0]) for b in cert["boxes"]) == 0
    v = _claims(checked, spec, ["stable_for_small_cfl"])["stable_for_small_cfl"]
    assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["von_neumann_small_cfl"]


def test_spec_verdicts():
    want = {"advection-upwind": C.VERIFIED, "advection-lax-friedrichs": C.VERIFIED,
            "advection-lax-wendroff": C.VERIFIED, "broken-advection-ftcs": C.REFUTED}
    for name, verdict in want.items():
        assert "stable_for_small_cfl" in _spec(name)["named_claims"]
        v = {x["claim"]: x for x in check(_spec(name), (100, 200), (200, 400))["claims"]}
        assert v["stable_for_small_cfl"]["verdict"] == verdict
        assert not [c for c, x in v.items() if x["verdict"] == C.INCONSISTENT]


def test_small_cfl_agrees_with_fixed_range_von_neumann():
    """VERIFIED on [0, nu0] by this check is the von Neumann check on that range; a refutation here means
    the fixed-range check refutes [0, nu] for every nu > 0 (spot: nu = nu1/2)."""
    decided = 0
    for path in SPECS:
        spec = load(path)
        r = linear.von_neumann_small_cfl(spec)
        if r["status"] not in (checks.VERIFIED, checks.REFUTED):
            continue
        decided += 1
        sign = 1 if linear.coefficients(spec, "x", "x")[0][0] > 0 else -1
        nu = Fraction(r["witness"]["nu0"] if r["status"] == checks.VERIFIED else r["witness"]["refutation"]["nu1"])
        nu = nu * sign if r["status"] == checks.VERIFIED else nu * sign / 2
        rng = [str(min(0, nu)), str(max(0, nu))]
        assert linear.von_neumann({**spec, "claims": {"von_neumann_cfl": rng}})["status"] == r["status"], path.stem
    assert decided >= 10


def test_negative_speed_uses_the_physical_sign():
    """a = -1 with F = uL is inconsistent, but its update u0 - lam (u0 - um1) is the stable upwind form in
    s = lam = -nu: VERIFIED. The downwind flux for a = 1 is unstable for every nu > 0: REFUTED."""
    r = linear.von_neumann_small_cfl(_spec("broken-advection-inconsistent-flux"))
    assert r["status"] == checks.VERIFIED and "s = |nu| = -nu" in r["witness"]
    r = linear.von_neumann_small_cfl(_spec("broken-advection-downwind"))
    assert r["status"] == checks.REFUTED and r["witness"]["refutation"]["k (lowest power of nu)"] == 1


def test_zeros_of_the_lowest_term_are_not_read_as_stability(monkeypatch):
    """G = nu^2 (1 - z)^2 - nu^3 (1 - z) = nu^2 w (w - nu), w = 1 - z: the lowest term q_2 = w^2 is >= 0
    but vanishes at z = 1, and G < 0 for 0 < w < nu, so the claim is false at every nu0. No rational z
    has q_2(z) < 0 and no certificate exists: the check must say UNKNOWN, not VERIFIED. (No three-point
    spec on disk has this G, so it is put in place of |g|^2.)"""
    w = P.add(P.const(1), linear.Z, -1)
    G = P.add(P.mul(P.power(linear.NU, 2), P.power(w, 2)), P.mul(P.power(linear.NU, 3), w), -1)
    monkeypatch.setattr(linear, "amplification_squared", lambda c: P.add(P.const(1), G, -1))
    r = linear.von_neumann_small_cfl(_spec("advection-upwind"))
    assert r["status"] == checks.UNKNOWN and r["witness"]["lowest term"] == {"k": 2, "q_k(z)": P.show(P.power(w, 2))}
    grid = linear._grid(G)
    for nu in (Fraction(1, 2), Fraction(1, 64), Fraction(1, 1024)):   # z = 1 - nu^2: G = nu^5 (nu - 1) < 0
        assert linear._value(grid, nu, 1 - nu ** 2) < 0


def test_small_cfl_row():
    (row,) = C.CLAIMS["stable_for_small_cfl"][1]
    assert row[:2] == ("von_neumann_small_cfl", C.EQUIVALENT) and C.GUARANTEE[row[0]] == C.EXACT
    assert "max norm included" in row[2] and "eigenvectors" in row[2]
    nonlinear = _spec("burgers-lax-friedrichs")
    assert linear.von_neumann_small_cfl(nonlinear)["status"] == checks.NOT_APPLICABLE
