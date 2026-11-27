"""The exact NECESSARY rows for limit_is_weak_solution, selects_entropy_solution and correct_shock_speed:
a stationary jump that violates Rankine-Hugoniot (fixedjump.py). The shock-speed row sees only frozen Lax
shocks."""

from __future__ import annotations

import copy
from fractions import Fraction
from pathlib import Path

import pytest

from physverify.schemes import checks, claims as C, fixedjump, limiters, load, poly as P, shockspeed, systems

ROOT = Path(__file__).resolve().parents[1]
S = ROOT / "schemes"
CLAIMS = ("limit_is_weak_solution", "correct_shock_speed", "selects_entropy_solution")
# freezes exactly the pairs with uL < uR (expansions): at (a, a, b) and (a, b, b) both min(., 0) terms are
# min(b - a, 0), which is 0 iff a <= b; so 0 | 1 is a fixed point at every window, and 1 | 0 is not
FROZEN_EXPANSION = "u0 - lam*((up1 - u0 - abs(up1 - u0))/2 + (u0 - um1 - abs(u0 - um1))/2)"


def _burgers(**scheme) -> dict:
    return {"name": "test", "pde": {"flux": "u^2/2"}, "scheme": scheme, "claims": {}}


def _exact(spec: dict) -> list[dict]:
    """Every exact check the claims' rows look at."""
    out = [checks.consistency(spec), checks.conservation(spec), shockspeed.flux_lipschitz(spec),
           shockspeed.shock_scope_monotone(spec), shockspeed.shock_scope_tvd(spec),
           fixedjump.stationary_rh_violation(spec), fixedjump.stationary_shock_rh_violation(spec),
           checks.steady_nonentropy_step(spec)]
    if "monotone_cfl" in spec["claims"]:
        out.append(checks.monotonicity(spec))
    if "tvd_cfl" in spec["claims"]:
        out.append(limiters.tvd_harten(spec))
    return out


def test_quasilinear_upwind_burgers_is_refuted_with_the_pair():
    spec = load(S / "broken-burgers-nonconservative.json")
    r = fixedjump.stationary_rh_violation(spec)
    assert r["status"] == checks.REFUTED
    w = r["witness"]
    assert (w["uL"], w["uR"], w["f(uL)"], w["f(uR)"]) == ("1", "0", "1/2", "0")
    assert w["Rankine-Hugoniot speed"] == "1/2" and w["found_by"] == "shock-study pair"
    # the replay: H(1, 1, 0) = 1 and H(1, 0, 0) = 0 at the study's dt/dx
    assert w["replay"]["H(1, 1, 0) at dt/dx = 4/5"] == "1" and w["replay"]["H(1, 0, 0) at dt/dx = 4/5"] == "0"
    # 1 | 0 is a Lax shock of Burgers, so the shock-speed check refutes with the same pair
    s = fixedjump.stationary_shock_rh_violation(spec)
    assert s["status"] == checks.REFUTED
    assert (s["witness"]["uL"], s["witness"]["uR"]) == ("1", "0")
    assert s["witness"]["Lax shock"]["f'(uL)"] == "1" and s["witness"]["Lax shock"]["f'(uR)"] == "0"
    for name, check in (("limit_is_weak_solution", "stationary_rh_violation"),
                        ("selects_entropy_solution", "stationary_rh_violation"),
                        ("correct_shock_speed", "stationary_shock_rh_violation")):
        v = C.judge([name], _exact(spec))[0]
        assert v["verdict"] == C.REFUTED and v["guarantee"] == C.EXACT
        assert v["decided_by"] == [check]
        assert any("stationary jump is a weak solution iff f(uL) = f(uR)" in a for a in v["assumes"])
    v = C.judge(["correct_shock_speed"], _exact(spec))[0]
    assert any("Lax shock" in a for a in v["assumes"])


def test_frozen_expansion_refutes_the_weak_limit_but_not_the_shock_speed():
    """0 | 1 for Burgers is an expansion (f'(0) = 0 < f'(1) = 1): the exact solution is a rarefaction, with no
    shock in it. Freezing it gives a limit that is no weak solution (f(0) = 0 != f(1) = 1/2), so the weak-limit
    and entropy claims are refuted, but it shows no shock at a wrong speed, so correct_shock_speed is not."""
    spec = _burgers(update=FROZEN_EXPANSION)
    spec["claims"] = {"shock_speed": {"cases": [{"uL": "0", "uR": "1", "T": "1", "lam": "1/2"}]}}
    H = P.from_expr(checks.update(spec))
    for lam in (Fraction(1, 3), Fraction(1, 2), Fraction(3)):        # 0 | 1 is a fixed point at every window
        at = lambda a, b, c: P.evaluate(H, {"um1": Fraction(a), "u0": Fraction(b), "up1": Fraction(c), "lam": lam})
        assert (at(0, 0, 0), at(0, 0, 1), at(0, 1, 1), at(1, 1, 1)) == (0, 0, 1, 1)
        assert at(1, 1, 0) != 1                                       # 1 | 0 is not
    r = fixedjump.stationary_rh_violation(spec)
    assert r["status"] == checks.REFUTED
    assert (r["witness"]["uL"], r["witness"]["uR"], r["witness"]["found_by"]) == ("0", "1", "shock-study pair")
    assert fixedjump.stationary_shock_rh_violation(spec)["status"] == checks.NOT_APPLICABLE
    verdicts = {v["claim"]: v for v in C.judge(CLAIMS, _exact(spec))}
    assert verdicts["limit_is_weak_solution"]["verdict"] == C.REFUTED
    assert verdicts["selects_entropy_solution"]["verdict"] == C.REFUTED
    assert "stationary_rh_violation" in verdicts["selects_entropy_solution"]["decided_by"]
    assert verdicts["correct_shock_speed"]["verdict"] not in C.FAILURES
    # with monotonicity run too, the Crandall-Majda row cannot fire (not conservative): no INCONSISTENT
    spec["claims"]["monotone_cfl"] = "1/3"
    assert all(v["verdict"] != C.INCONSISTENT for v in C.judge(CLAIMS, _exact(spec)))


def test_expansion_pair_is_not_a_lax_shock():
    f = P.from_expr(checks.pde_flux(_burgers(update="u0")))
    assert fixedjump.lax_shock(f, Fraction(1), Fraction(0)) is not None
    assert fixedjump.lax_shock(f, Fraction(0), Fraction(1)) is None
    # u^3 is convex on [0, 1] but not on [-1, 1]: 1 | -1 has f'(1) = f'(-1), and 1/2 | -1 has f'(1/2) < f'(-1)
    g = P.from_expr(checks.pde_flux({"pde": {"flux": "u^3"}}))
    assert fixedjump.lax_shock(g, Fraction(1), Fraction(0)) is not None
    assert fixedjump.lax_shock(g, Fraction(1), Fraction(-1)) is None
    assert fixedjump.lax_shock(g, Fraction(1), Fraction(-1, 2)) is None   # f' drops 3 > 3/4, but f'' < 0 on [-1/2, 0)


def test_identity_update_freezes_shocks_too():
    """u^{n+1} = u^n freezes every pair, a Lax shock among them, so the shock-speed row refutes."""
    r = fixedjump.stationary_shock_rh_violation(_burgers(update="u0"))
    assert r["status"] == checks.REFUTED
    assert Fraction(r["witness"]["uL"]) > Fraction(r["witness"]["uR"])


def test_the_jump_cell_by_hand():
    """At the jump cell u0 = 0: 0 - lam*0*(0 - 1) = 0; upstream u0 = um1 = 1, so u0 - um1 = 0."""
    H = P.from_expr(checks.update(load(S / "broken-burgers-nonconservative.json")))
    for lam in (Fraction(1, 3), Fraction(4, 5), Fraction(7)):
        at = lambda a, b, c: P.evaluate(H, {"um1": Fraction(a), "u0": Fraction(b), "up1": Fraction(c), "lam": lam})
        assert (at(1, 1, 1), at(1, 1, 0), at(1, 0, 0), at(0, 0, 0)) == (1, 1, 0, 0)


def test_five_point_quasilinear_upwind_is_refuted():
    u = "u0 - lam*((u0 + abs(u0))/2*(3*u0 - 4*um1 + um2)/2 + (u0 - abs(u0))/2*(-up2 + 4*up1 - 3*u0)/2)"
    r = fixedjump.stationary_rh_violation(_burgers(update=u))
    assert r["status"] == checks.REFUTED and r["witness"]["stencil"] == list(checks.STENCIL5)
    assert len(r["witness"]["identities"]) == 6                # 2 far-field windows + 4 across the jump


@pytest.mark.parametrize("spec", [
    _burgers(numerical_flux="uL^2/2"),                              # conservative upwind (for u >= 0)
    _burgers(update="u0 - lam*(u0^2/2 - um1^2/2)"),                 # the same, as an update
    load(S / "burgers-lax-friedrichs.json"), load(S / "burgers-rusanov.json"),
    load(S / "burgers-engquist-osher.json"), load(ROOT / "benchmark/scheme-claims/specs/burgers-godunov.json"),
], ids=["upwind-flux", "upwind-update", "lxf", "rusanov", "engquist-osher", "godunov"])
def test_conservative_burgers_schemes_are_never_refuted(spec):
    assert fixedjump.stationary_rh_violation(spec)["status"] == checks.NOT_APPLICABLE
    assert fixedjump.stationary_shock_rh_violation(spec)["status"] == checks.NOT_APPLICABLE


def test_roe_transonic_expansion_is_a_fixed_jump_but_a_weak_solution():
    """Roe without an entropy fix freezes -1 | 1 (a = 0 at the jump), but f(-1) = f(1): the frozen step is a
    weak solution (not the entropy one), so this check must not refute."""
    spec = load(S / "broken-burgers-roe-no-entropy-fix.json")
    H = P.from_expr(checks.update(spec))
    ids = fixedjump._identities(H, checks.STENCIL, Fraction(-1), Fraction(1))
    assert not any(ids.values())                                  # it is a fixed point ...
    assert fixedjump.stationary_rh_violation(spec)["status"] == checks.NOT_APPLICABLE   # ... and not refuted
    assert checks.steady_nonentropy_step(spec)["status"] == checks.REFUTED            # the entropy row sees it


def test_windows():
    assert fixedjump.windows(checks.STENCIL) == [("LLL", "L"), ("RRR", "R"), ("LLR", "L"), ("LRR", "R")]
    assert [c for _, c in fixedjump.windows(checks.STENCIL5)] == ["L", "R", "L", "L", "R", "R"]


def _scalar_specs():
    paths = sorted(S.rglob("*.json")) + sorted((ROOT / "benchmark/scheme-claims/specs").glob("*.json"))
    return [p for p in paths if not systems.is_system(load(p))]


@pytest.mark.parametrize("path", _scalar_specs(), ids=lambda p: p.stem)
def test_no_sufficient_row_verifies_what_the_fixed_jump_refutes(path):
    """A SUFFICIENT row VERIFYING a claim this check REFUTES would be INCONSISTENT: never on any spec here."""
    spec = copy.deepcopy(load(path))
    spec.setdefault("claims", {})
    results = _exact(spec)                          # the same exact checks for every claim: run them once
    for name in CLAIMS:
        v = C.judge([name], copy.deepcopy(results))[0]
        assert v["verdict"] != C.INCONSISTENT, v["detail"]


def test_judge_reports_inconsistent_if_both_fire():
    fake = [{"check": "conservation", "status": C.VERIFIED}, {"check": "consistency", "status": C.VERIFIED},
            {"check": "flux_lipschitz", "status": C.VERIFIED}, {"check": "stationary_rh_violation", "status": C.REFUTED}]
    assert C.judge(["limit_is_weak_solution"], fake)[0]["verdict"] == C.INCONSISTENT
    na = fake[:3] + [{"check": "stationary_rh_violation", "status": checks.NOT_APPLICABLE}]
    assert C.judge(["limit_is_weak_solution"], na)[0]["verdict"] == C.VERIFIED
