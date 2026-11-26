"""The exact rows for correct_shock_speed (Crandall-Majda; Helly + Lax-Wendroff for TVD schemes), the
Lax-Wendroff row for limit_is_weak_solution, and their preconditions (shockspeed.py). The empirical
shock study is left out here (it is slow on five-point stencils); these rows do not use it."""

from __future__ import annotations

import copy
from pathlib import Path

from physverify.schemes import checks, claims as C, limiters, load, shockspeed

S = Path(__file__).resolve().parents[1] / "schemes"


def _exact(spec: dict) -> list[dict]:
    """The exact checks the three rows look at."""
    out = [checks.consistency(spec), checks.conservation(spec), shockspeed.flux_lipschitz(spec),
           shockspeed.shock_scope_monotone(spec), shockspeed.shock_scope_tvd(spec)]
    if "monotone_cfl" in spec["claims"]:
        out.append(checks.monotonicity(spec))
    if "tvd_cfl" in spec["claims"]:
        out.append(limiters.tvd_harten(spec))
    return out


def _verdict(name: str, results: list[dict]) -> dict:
    return C.judge([name], results)[0]


def _with_cases(spec: dict, *lams: str) -> dict:
    spec = copy.deepcopy(spec)
    spec["claims"]["shock_speed"] = {"x0": "1/4", "cases": [{"uL": "1", "uR": "0", "T": "1/2", "lam": l} for l in lams]}
    return spec


def test_row_a_lax_friedrichs_burgers_is_verified():
    spec = load(S / "burgers-lax-friedrichs.json")
    v = _verdict("correct_shock_speed", _exact(spec))
    assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["monotonicity"]
    assert any("Crandall-Majda" in a and "Rankine-Hugoniot" in a for a in v["assumes"])


def test_row_a_needs_the_study_inside_the_certified_monotone_range():
    spec = load(S / "burgers-lax-friedrichs.json")
    spec["claims"]["shock_speed"]["cases"][0]["lam"] = "3/2"        # 3/2 * |f'(1)| > 1
    assert shockspeed.shock_scope_monotone(spec)["status"] == checks.NOT_APPLICABLE
    v = _verdict("correct_shock_speed", _exact(spec))
    assert v["verdict"] == C.UNKNOWN
    assert v["evidence"][0]["unmet"] == ["shock_scope_monotone: NOT_APPLICABLE"]
    # Rusanov is certified monotone only up to 1/3, and its study runs at 4/5
    rus = load(S / "burgers-rusanov.json")
    assert _verdict("correct_shock_speed", _exact(rus))["verdict"] == C.UNKNOWN


def test_row_a_needs_conservation():
    spec = load(S / "broken-burgers-nonconservative.json")
    v = _verdict("correct_shock_speed", _exact(spec))
    assert v["verdict"] == C.UNKNOWN and any(u.startswith("conservation") for u in v["evidence"][0]["unmet"])


def test_row_b_fires_on_minmod_inside_the_tvd_range():
    spec = _with_cases(load(S / "limiters" / "advection-minmod.json"), "1/2", "37/100")
    v = _verdict("correct_shock_speed", _exact(spec))
    assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["tvd_harten"]
    note = " ".join(v["assumes"])
    for words in ("Subsequence only", "entropy-violating discontinuity", "nothing about uniqueness or entropy",
                  "Helly", "Lax-Wendroff"):
        assert words in note


def test_row_b_unknown_when_a_precondition_fails():
    base = _with_cases(load(S / "limiters" / "advection-minmod.json"), "1/2")
    out = _with_cases(base, "3/2")                                    # nu = 3/2 outside [0, 1]
    v = _verdict("correct_shock_speed", _exact(out))
    assert v["verdict"] == C.UNKNOWN and v["evidence"][0]["unmet"] == ["shock_scope_tvd: NOT_APPLICABLE"]
    none = copy.deepcopy(base)
    del none["claims"]["shock_speed"]                                 # no study dt/dx at all
    assert _verdict("correct_shock_speed", _exact(none))["verdict"] == C.UNKNOWN
    # the same exact results with conservation or the Lipschitz check not verified
    results = _exact(base)
    for drop in ("conservation", "consistency", "flux_lipschitz"):
        rs = [r if r["check"] != drop else {**r, "status": checks.UNKNOWN} for r in results]
        v = _verdict("correct_shock_speed", rs)
        assert v["verdict"] == C.UNKNOWN and v["evidence"][0]["unmet"] == [f"{drop}: UNKNOWN"]


def test_empirical_shock_study_alone_never_verifies():
    study = checks.result("shock_speed", "NOT_REFUTED", "shock speed")
    assert _verdict("correct_shock_speed", [study])["verdict"] == C.NOT_REFUTED
    assert _verdict("limit_is_weak_solution", [study])["verdict"] == C.UNKNOWN


def test_limit_is_weak_solution_row():
    lf = load(S / "burgers-lax-friedrichs.json")
    v = _verdict("limit_is_weak_solution", _exact(lf))
    assert v["verdict"] == C.VERIFIED and v["decided_by"] == ["conservation"]
    assert any("Lax-Wendroff theorem (1960)" in a for a in v["assumes"])
    for bad in ("broken-burgers-nonconservative", "broken-burgers-scaled-flux"):   # not conservative; inconsistent
        assert _verdict("limit_is_weak_solution", _exact(load(S / f"{bad}.json")))["verdict"] == C.UNKNOWN


def _lip(flux: str, update: bool = False) -> str:
    spec = {"pde": {"flux": "u^2/2"}, "scheme": {("update" if update else "numerical_flux"): flux}}
    return shockspeed.flux_lipschitz(spec)["status"]


def test_flux_lipschitz_by_form():
    for ok in ("(uL^2 + uR^2)/4 - (uR - uL)/(2*lam)", "max(uL, 0)^2/2 + min(uR, 0)^2/2",
               "uL + (1 - lam)/2*minmod(uR - uL, uL - uLL)", "abs(uL - uR)^3", "uL/2"):
        assert _lip(ok) == checks.VERIFIED, ok
    for bad in ("sqrt(uL^2 + uR^2)", "sqrt(uL)", "uL/uR", "(uL^2 - uR^2)/(uL - uR)", "uL^(1/2)", "sin(uL)",
                "uL^(-1)", "uL/(lam - lam)"):
        assert _lip(bad) == checks.UNKNOWN, bad
    assert _lip("u0 - lam*(u0^2 - um1^2)/2", update=True) == checks.VERIFIED
    assert _lip("u0 - lam*u0*(u0 - um2)", update=True) == checks.UNKNOWN          # five-point update, no flux
