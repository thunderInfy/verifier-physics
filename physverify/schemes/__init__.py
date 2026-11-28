"""Checks for discrete schemes: a numerical scheme is a theory of a discrete universe.

`check(spec)` runs the exact structural checks (`checks.py`) and the empirical convergence
studies (`convergence.py`, `shock.py`, `entropy.py`) that the spec asks for. It returns
{"checks": [raw result dicts], "claims": [one verdict per named claim]}. The spec declares its
named claims (`named_claims`); the trusted table in `claims.py` decides what each check result
means for them.
"""

from __future__ import annotations

import json
from pathlib import Path

from . import checks, claims, convergence, entropy, fixedjump, identity, limiters, linear, shock, shockspeed, ssp, systems
from . import ssp_class

CLASS_ONLY = {"ssp_class_preserves": ssp_class.ssp_class, "ssp_coefficient": ssp_class.ssp_coefficient}


def load(path) -> dict:
    return json.loads(Path(path).read_text())


def check(spec: dict, shock_grids=shock.GRIDS, rarefaction_grids=entropy.GRIDS) -> dict:
    names = spec.get("named_claims", [])
    claims.validate(names)
    if names and set(names) <= set(CLASS_ONLY):          # claims about Runge-Kutta coefficients alone: no scheme
        out = [f(spec) for n, f in CLASS_ONLY.items() if n in names]
        return {"checks": out, "claims": claims.judge(names, out)}
    if systems.is_system(spec):
        out = systems.check_all(spec)
        return {"checks": out, "claims": claims.judge(names, out)}
    params = spec.get("claims", {})
    wanted = {c for n in names for c, *_ in claims.CLAIMS[n][1]}
    out = [checks.consistency(spec), checks.conservation(spec), checks.positivity(spec)]
    if "test" in spec:
        out += convergence.studies(spec)
    if "shock_speed" in params:
        out.append(shock.study(spec, shock_grids))
    if "entropy_stability" in params or "entropy_stability" in wanted:
        # a named claim can need Tadmor's check without the spec claiming it: run it with the defaults
        out.append(checks.entropy_stability({**spec, "claims": {"entropy_stability": {}, **params}}))
    if "monotone_cfl" in params or "monotone_under_cfl" in names:
        out.append(checks.monotonicity(spec))
    if "steady_nonentropy_step" in wanted:
        out.append(checks.steady_nonentropy_step(spec))
    if "steady_nonentropy_step_semidiscrete" in wanted:
        out.append(checks.steady_nonentropy_step_semidiscrete(spec))
    if "stationary_rh_violation" in wanted:
        out.append(fixedjump.stationary_rh_violation(spec))
    if "stationary_shock_rh_violation" in wanted:
        out.append(fixedjump.stationary_shock_rh_violation(spec))
    if "entropy_rarefaction" in params:
        out.append(entropy.study(spec, rarefaction_grids))
    if "consistent_order" in params or "consistent_order_p" in names:
        out.append(linear.truncation_order(spec))
        if "converges_order_p" in names:
            out.append(linear.lax_richtmyer_scope(spec))
    if "von_neumann_cfl" in params or "von_neumann_stable_under_cfl" in names:
        out.append(linear.von_neumann(spec))
    if "von_neumann_small_cfl" in wanted:
        out.append(linear.von_neumann_small_cfl(spec))
    if "tvd_cfl" in params or {"tvd_under_cfl", "local_max_principle_under_cfl"} & set(names):
        out += [limiters.tvd_harten(spec), limiters.tv_increase(spec), linear.tvd_linear(spec)]
    if "local_max_principle_under_cfl" in names:
        out += [limiters.max_principle_violation(spec), linear.max_principle_linear(spec)]
    if "stated_identity" in params or "stated_identity" in names:
        out.append(identity.stated_identity(spec))
    if "smooth_truncation" in params or "truncation_order_smooth_data" in names:
        out += [limiters.truncation_branches(spec), limiters.truncation_smooth_data(spec)]
    if "ssp" in params or "ssp_preserves" in names:
        out += [ssp.ssp(spec), ssp.ssp_linear(spec), ssp.ssp_violation(spec)]
    out += [f(spec) for n, f in CLASS_ONLY.items() if n in names]
    # preconditions of the convergence rows for correct_shock_speed and limit_is_weak_solution
    out += [f(spec) for c, f in (("flux_lipschitz", shockspeed.flux_lipschitz),
                                 ("shock_scope_monotone", shockspeed.shock_scope_monotone),
                                 ("shock_scope_tvd", shockspeed.shock_scope_tvd))
            if any(c in row[3] for n in names for row in claims.CLAIMS[n][1] if len(row) > 3)]
    return {"checks": out, "claims": claims.judge(names, out)}


FAILURES = (checks.REFUTED, convergence.REFUTED_EMPIRICALLY, convergence.SUSPICIOUS)


def failed(report: dict) -> list[str]:
    """The failing named claims; with no named claims, the failing raw checks."""
    if report["claims"]:
        return [v["claim"] for v in report["claims"] if v["verdict"] in claims.FAILURES]
    return [r["check"] for r in report["checks"] if r["status"] in FAILURES]


def render(spec: dict, report: dict) -> str:
    bad, results = failed(report), report["checks"]
    lines = [f"## {spec['name']}: " + (f"FAILS {', '.join(bad)}" if bad else "no claim refuted")]
    if report["claims"]:
        lines.append("claims (judged by the table in claims.py):")
    for v in report["claims"]:
        g = f", {v['guarantee']}" if v["guarantee"] else ""
        loud = "!!! " if v["verdict"] == claims.INCONSISTENT else ""
        lines.append(f"- {loud}[{v['verdict']}] ({v['claim']}{g}) {v['statement']}")
        ev = "; ".join(f"{e['check']} {e['relation']} {e['status']} -> {e['gives']}"
                       + (f" (requires {', '.join(e['unmet'])})" if e.get("unmet") else "") for e in v["evidence"])
        lines.append(f"    evidence: {ev or 'none'}")
        if v["detail"]:
            lines.append(f"    {v['detail']}")
        for a in v["assumes"]:
            lines.append(f"    assumes: {a}")
    if report["claims"]:
        lines.append("checks (raw evidence):")
    for r in results:
        g = f", {r['guarantee']}" if r["guarantee"] else ""
        lines.append(f"- [{r['status']}] ({r['check']}{g}) {r['claim']}")
        if r["detail"]:
            lines.append(f"    {r['detail']}")
        for a in r["assumptions"]:
            lines.append(f"    assumes: {a}")
        w = r["witness"]
        if "table" in w:
            lines.append(f"    study: {w['study']}")
            lines += [f"      {row}" for row in w["table"]]
        elif w:
            for k, v in w.items():
                lines.append(f"    {k}: {v}")
    return "\n".join(lines)
