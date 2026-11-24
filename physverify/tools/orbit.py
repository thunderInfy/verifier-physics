"""Step 6 — orbit existence (weak anthropic principle, phrased weakly).

Existence fact: a body's distance r(t) has a perihelion (local min) and an aphelion
(local max) inside the observed boxes. `PhysVerify.EccentricExcluded.refutes` shows a central
force law cannot produce that if h(r) = r³ f(r) is smaller at every admissible aphelion than at
every admissible perihelion — for any angular momentum.
"""

from __future__ import annotations

from .. import lean_terms as lt
from ..core import PROVEN, Candidate
from ..theory import Evidence, Theory
from .binding import bind

NAME = "orbit"

_FINISH = """first
  | linarith
  | (rw [div_lt_one hy0]; linarith)
  | (rw [div_lt_one hx0]; linarith)
  | nlinarith [mul_pos hx0 hy0, hxy]"""


def _orbit_spec(th: Theory, ev: Evidence):
    o = ev.extra.get("orbit")
    if not o or not th.central_force:
        return None
    rsym, f = th.central_force
    (a1, b1), (a2, b2) = ev.bounds[o["perihelion"]], ev.bounds[o["aphelion"]]
    params = {s: b for s, b in bind(th, ev).items() if s != rsym}
    positive = sorted(s for s in th.positive if s not in params and s != rsym)
    return rsym, f, (a1, b1, a2, b2), params, positive


def obligation(args, th: Theory, evidence: dict[str, Evidence]):
    from ..obligations import Obligation, in_regime  # avoid import cycle
    ev = evidence[args["evidence"]]
    spec = _orbit_spec(th, ev)
    if spec is None:
        raise KeyError("theory has no central_force or evidence has no orbit")
    rsym, f, (a1, b1, a2, b2), params, positive = spec
    why = in_regime(th, {**params, rsym: (a1, b2)})
    if why:
        return Obligation(why, "", [], [ev.id], skip="OUT_OF_REGIME")
    idx = lt.index(th)
    hyps, _ = lt.bound_hyps(th, params)
    prem = [hyps] if hyps else []
    prem += [f"0 < env {idx[s]}" for s in positive]
    prem_s = " → ".join(prem) + " → " if prem else ""
    stmt = (f"∀ env : ℕ → ℝ, {prem_s}EccentricExcluded {lt.expr(f, th)} {idx[rsym]} env "
            f"{lt.real(a1)} {lt.real(b1)} {lt.real(a2)} {lt.real(b2)}")
    o = ev.extra["orbit"]
    return Obligation(
        claim=(f"force law f({rsym}) = {f!r} admits no orbit with perihelion in "
               f"[{float(a1):.4g}, {float(b1):.4g}] and aphelion in [{float(a2):.4g}, {float(b2):.4g}]"),
        guarantee=PROVEN,
        assumptions=[
            "Newtonian central-force radial equation r'' = ℓ²/r³ − f(r) (two-body reduction)",
            f"{ev.id}: r(t) has a local min ({o['perihelion']}) and a local max ({o['aphelion']}) "
            f"inside the stated bounds ({ev.source})",
        ] + ([f"{ev.id}: hard bounds on {', '.join(sorted(params))}"] if params else []),
        evidence=[ev.id],
        statement=stmt,
        conclusion="PhysVerify.EccentricExcluded.refutes",
    )


def _promising(th: Theory, spec) -> bool:
    """Cheap untrusted pre-filter: is h(r) = r³ f(r) smaller at aphelion than at perihelion?"""
    from .enclosure import _box, ieval
    from mpmath import iv
    rsym, f, (a1, b1, a2, b2), params, positive = spec
    env = {s: _box(lo, hi).mid for s, (lo, hi) in params.items()}
    env.update({s: iv.mpf(1) for s in positive})
    try:
        h = lambda r: float((r ** 3 * ieval(f, {**env, rsym: iv.mpf(r)})).mid)
        x, y = float((a1 + b1) / 2), float((a2 + b2) / 2)
        return h(y) < h(x)
    except Exception:
        return True  # can't tell: let Lean decide


def propose(th: Theory, evidence: list[Evidence]) -> list[Candidate]:
    out = []
    for ev in evidence:
        spec = _orbit_spec(th, ev)
        if spec is None or not _promising(th, spec):
            continue
        _, _, _, params, positive = spec
        names = [f"h_{s}" for s in sorted(params)] + [f"hp_{s}" for s in positive]
        proof = "\n".join([
            f"intro env {' '.join(names)} x hx y hy",
            "simp only [Set.mem_Icc] at hx hy",
            "have hx0 : 0 < x := by linarith",
            "have hy0 : 0 < y := by linarith",
            "have hxy : x < y := by linarith",
            "simp [hExpr, Expr.eval, Function.update_apply]",
            "field_simp",
            _FINISH,
        ])
        out.append(Candidate(NAME, "orbit_excluded", {"evidence": ev.id}, proof,
                             note="generic monotonicity script"))
    return out
