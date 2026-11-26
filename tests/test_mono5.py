"""Monotonicity and the steady non-entropy step on five-point stencils (limiters.monotonicity_wide and the
wide branch of checks.steady_nonentropy_step). Every refutation is replayed here from a reference
implementation of the scheme written independently of the checker, in Fraction arithmetic."""
from fractions import Fraction as Fr
from pathlib import Path

import pytest

from physverify.schemes import check, checks, claims as C, limiters as L, load, poly as P

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes" / "limiters"
STENCIL = ("um2", "um1", "u0", "up1", "up2")


def minmod(a, b):
    return min(a, b) if a > 0 and b > 0 else max(a, b) if a < 0 and b < 0 else Fr(0)


def minmod_slope(d_right, d_left):
    return minmod(d_right, d_left)


def superbee_slope(d_right, d_left):
    m1, m2 = minmod(2 * d_right, d_left), minmod(d_right, 2 * d_left)
    return max(m1, m2) if m1 >= 0 and m2 >= 0 else min(m1, m2)       # maxmod: m1, m2 never differ in sign


def sweby_H(u: dict, nu, slope):
    """u_i^{n+1} for a = 1, F_{i+1/2} = u_i + (1 - nu)/2 * slope(u_{i+1} - u_i, u_i - u_{i-1})."""
    um2, um1, u0, up1 = (u[k] for k in ("um2", "um1", "u0", "up1"))
    F = lambda l2, l, r: l + (1 - nu) / 2 * slope(r - l, l - l2)
    return u0 - nu * (F(um1, u0, up1) - F(um2, um1, u0))


def _mono(name, **claims):
    spec = load(S / f"{name}.json")
    spec["claims"] = {**spec.get("claims", {}), **claims}
    return spec


def _pair(r):
    w = r["witness"]["counterexample"]
    u = {k: Fr(v) for k, v in w["u"].items()}
    v = {k: Fr(x) for k, x in w["v"].items()}
    return w, u, v, Fr(w["nu"])


# ---------------------------------------------------------------- monotonicity

@pytest.mark.parametrize("name,slope", [("broken-advection-minmod-monotone", minmod_slope),
                                        ("broken-advection-superbee-monotone", superbee_slope)])
def test_limited_schemes_are_not_monotone(name, slope):
    """Godunov's theorem in action: minmod and superbee are TVD on [0, 1] but not monotone. The witness
    is two states u <= v strictly inside one full-dimensional sign cell with H(u) > H(v)."""
    r = checks.monotonicity(load(S / f"{name}.json"))
    assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
    w, u, v, nu = _pair(r)
    assert 0 < nu <= 1
    assert all(u[k] <= v[k] for k in STENCIL) and sum(v[k] != u[k] for k in STENCIL) == 1
    Hu, Hv = sweby_H(u, nu, slope), sweby_H(v, nu, slope)
    assert Hu > Hv and (str(Hu), str(Hv)) == (w["H(u)"], w["H(v)"])
    # both states lie strictly inside the cell the checker used (where H is one polynomial)
    cell = L.cells(checks.update(load(S / f"{name}.json")))["cells"][w["cell index"]]
    assert all(P.evaluate(a, s) > 0 for a in cell["atoms"] for s in (u, v))
    assert Fr(w[f"dH/d{w['increased']}" + " at nu"]) < 0
    counts = r["witness"]["cell_counts"]
    assert counts["retained (full-dimensional)"] == {"broken-advection-minmod-monotone": 18,
                                                     "broken-advection-superbee-monotone": 50}[name]


def test_minmod_is_monotone_only_at_nu_one():
    """On every minmod cell each partial is a polynomial in nu alone. At nu = 1 they are all >= 0 (the
    limited term carries the factor 1 - nu, so the scheme is upwind there), while some is negative at
    nu = 1/2: the claim on [0, 1] fails, but not at the endpoint."""
    neg = 0
    for c in L.cells(checks.update(load(S / "broken-advection-minmod-monotone.json")))["cells"]:
        Hc = L._in_nu(c["poly"], Fr(1))
        for x in STENCIL:
            d = P.derivative(Hc, x)
            assert P.variables(d) <= {"nu"}
            assert P.evaluate(d, {"nu": Fr(1)}) >= 0
            neg += P.evaluate(d, {"nu": Fr(1, 2)}) < 0
    assert neg > 0


def test_upwind_on_the_five_point_stencil_is_monotone():
    """First-order upwind with um2, up2 as (unused) arguments: VERIFIED on [0, 1], the five partials are
    0, nu, 1 - nu, 0, 0, and the three-point check agrees."""
    spec = load(ROOT / "schemes" / "advection-upwind.json")
    r = L.monotonicity_wide(spec)
    assert r["status"] == checks.VERIFIED
    parts = {x: p[f"dH/d{x}"] for x, p in r["witness"]["cells"][0]["partials"].items()}
    assert parts == {"um2": "0", "um1": "nu", "u0": "-nu + 1", "up1": "0", "up2": "0"}
    assert checks.monotonicity(spec)["status"] == checks.VERIFIED


def test_a_genuinely_five_point_positive_scheme():
    """F = a*(uL + uLL)/2 gives H = (1 - nu/2) u_i + (nu/2) u_{i-2}: monotone for nu <= 2 (VERIFIED through
    the five-point dispatch), not for nu <= 3 (REFUTED, the pair replayed from the formula)."""
    spec = {"name": "two-cell upwind", "pde": {"flux": "a*u"}, "params": {"a": "1"},
            "scheme": {"numerical_flux": "a*(uL + uLL)/2"}, "claims": {"monotone_cfl": "2"}}
    assert checks.stencil_of(P.variables(P.from_expr(checks.update(spec)))) == checks.STENCIL5
    assert checks.monotonicity(spec)["status"] == checks.VERIFIED
    r = checks.monotonicity({**spec, "claims": {"monotone_cfl": "3"}})
    assert r["status"] == checks.REFUTED
    w, u, v, nu = _pair(r)
    H = lambda s: (1 - nu / 2) * s["u0"] + nu / 2 * s["um2"]
    assert 2 < nu <= 3 and w["increased"] == "u0" and H(u) > H(v)


def test_lax_wendroff_flux_limiter_form_is_not_monotone():
    """The broken LW flux-limiter spec (slope uR - uL, a three-point stencil): the three-point check refutes
    it, and so does the five-point one, with a replayed pair."""
    spec = _mono("broken-advection-lw-flux-form-tvd", monotone_cfl="1")
    assert checks.monotonicity(spec)["status"] == checks.REFUTED
    r = L.monotonicity_wide(spec)
    assert r["status"] == checks.REFUTED
    _, u, v, nu = _pair(r)
    lw = lambda s: s["u0"] - nu / 2 * (s["up1"] - s["um1"]) + nu ** 2 / 2 * (s["up1"] - 2 * s["u0"] + s["um1"])
    assert all(u[k] <= v[k] for k in STENCIL) and lw(u) > lw(v)


def test_entropy_claim_stays_unknown_when_monotonicity_fails():
    """Monotonicity is SUFFICIENT for selects_entropy_solution: failing it decides nothing."""
    row = next(r for r in C.CLAIMS["selects_entropy_solution"][1] if r[0] == "monotonicity")
    assert row[1] == C.SUFFICIENT
    spec = {**load(S / "broken-advection-minmod-monotone.json"),
            "named_claims": ["monotone_under_cfl", "selects_entropy_solution"]}
    v = {x["claim"]: x for x in check(spec)["claims"]}
    assert v["monotone_under_cfl"]["verdict"] == C.REFUTED
    s = v["selects_entropy_solution"]
    assert s["verdict"] == C.UNKNOWN
    assert {e["check"]: e["gives"] for e in s["evidence"]} == {"steady_nonentropy_step": C.UNKNOWN,
                                                                "monotonicity": C.UNKNOWN}


def test_past_the_cell_cap_the_check_is_unknown(monkeypatch):
    monkeypatch.setattr(L, "MAX_CELLS", 5)
    r = checks.monotonicity(load(S / "broken-advection-minmod-monotone.json"))
    assert r["status"] == checks.UNKNOWN and "giving up" in r["detail"]


def test_nonlinear_five_point_monotonicity_is_unknown():
    spec = {**load(S / "burgers-muscl-minmod-rusanov.json"), "claims": {"monotone_cfl": "1"}}
    r = checks.monotonicity(spec)
    assert r["status"] == checks.UNKNOWN and "linear advection" in r["detail"]


# ---------------------------------------------------------------- steady non-entropy step

def roe(a, b):
    return (a * a + b * b) / 4 - abs(a + b) / 4 * (b - a)


def rusanov(a, b):
    return (a * a + b * b) / 4 - max(abs(a), abs(b)) / 2 * (b - a)


def muscl(F):
    return lambda l2, l, r, r2: F(l + minmod(r - l, l - l2) / 2, r - minmod(r2 - r, r - l) / 2)


def fluxes(flux, u):
    """Interface fluxes F_{i+1/2}, i = -1..n-1, with two constant (transmissive) ghost cells each side."""
    g = [u[0]] * 2 + u + [u[-1]] * 2
    return [flux(g[i - 1], g[i], g[i + 1], g[i + 2]) for i in range(1, len(u) + 2)]


def step(flux, u, lam):
    F = fluxes(flux, u)
    return [u[i] - lam * (F[i + 1] - F[i]) for i in range(len(u))]


def test_muscl_roe_keeps_the_expansion_shock_exactly():
    """MUSCL-minmod with the Roe flux and no entropy fix: the step -1 | 1 is a fixed point of every window
    of the update and a steady state of the method of lines. Replayed: ten steps at several dt/dx leave
    the grid unchanged, and every interface flux is 1/2."""
    spec = load(S / "broken-burgers-muscl-minmod-roe-no-entropy-fix.json")
    for mode, n in (("discrete", 6), ("semidiscrete", 4)):
        r = checks.steady_nonentropy_step(spec, mode)
        assert r["status"] == checks.REFUTED and r["guarantee"] == checks.EXACT
        assert (r["witness"]["uL"], r["witness"]["uR"]) == ("-1", "1") and len(r["witness"]["identities"]) >= n
    flux = muscl(roe)
    u0 = [Fr(-1)] * 5 + [Fr(1)] * 5
    assert set(fluxes(flux, u0)) == {Fr(1, 2)}
    for lam in (Fr(1, 3), Fr(1, 2), Fr(1)):
        u = u0
        for _ in range(10):
            u = step(flux, u, lam)
        assert u == u0
    v = {x["claim"]: x["verdict"] for x in check(spec)["claims"]}
    assert v == {"consistent": C.VERIFIED, "conservative": C.VERIFIED, "selects_entropy_solution": C.REFUTED,
                 "selects_entropy_solution_semidiscrete": C.REFUTED}


def test_muscl_rusanov_does_not_keep_it():
    """MUSCL-minmod with the Rusanov flux moves the step (Rusanov's numerical viscosity opens the fan):
    no steady step is found, so the check, and the entropy claims, stay UNKNOWN."""
    spec = load(S / "burgers-muscl-minmod-rusanov.json")
    for mode in ("discrete", "semidiscrete"):
        assert checks.steady_nonentropy_step(spec, mode)["status"] == checks.UNKNOWN
    u0 = [Fr(-1)] * 5 + [Fr(1)] * 5
    assert step(muscl(rusanov), u0, Fr(1, 2)) != u0
    r = checks.entropy_stability({**spec, "claims": {"entropy_stability": {}}})
    assert r["status"] == checks.UNKNOWN and "two-point" in r["detail"]


def test_wide_windows():
    assert [s for _, s, _ in checks.STEADY_STENCILS5] == ["LLLLL", "LLLLR", "LLLRR", "LLRRR", "LRRRR", "RRRRR"]
    assert [t for _, _, t in checks.STEADY_STENCILS5] == ["L", "L", "L", "R", "R", "R"]
    assert [(a, b) for _, a, b in checks.STEADY_INTERFACES4] == [("LLLR", "LLLL"), ("LLRR", "LLLR"),
                                                                 ("LRRR", "LLRR"), ("RRRR", "LRRR")]
