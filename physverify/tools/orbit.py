"""Step 6 — orbit existence (weak anthropic principle, phrased weakly).

Existence fact: a body's distance r(t) has a perihelion (local min) and an aphelion
(local max) inside the observed boxes. `PhysVerify.EccentricExcluded.refutes` shows a central
force law cannot produce that if h(r) = r³ f(r) is smaller at every admissible aphelion than at
every admissible perihelion — for any angular momentum.
"""

from __future__ import annotations

from fractions import Fraction

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
            "Newton's second law under a central attraction of magnitude f(r) per unit mass, any f(r) and any "
            "angular momentum ℓ (a fixed centre, or two bodies in relative coordinates): the radial equation "
            "r'' = ℓ²/r³ − f(r)",
            f"{ev.id}: r(t) has a local min ({o['perihelion']}) and a local max ({o['aphelion']}) "
            f"inside the stated bounds ({ev.source})",
        ] + ([f"{ev.id}: hard bounds on {', '.join(sorted(params))}"] if params else []),
        evidence=[ev.id],
        statement=stmt,
        conclusion="PhysVerify.EccentricExcluded.refutes",
    )


def _qeval(e, env: dict[str, Fraction]) -> Fraction:
    """Exact value of a rational expression (+ - * /, integer powers); ValueError for anything else."""
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return Fraction(e.q)
    if k == "neg": return -_qeval(a[0], env)
    if k in ("add", "sub", "mul", "div"):
        x, y = _qeval(a[0], env), _qeval(a[1], env)
        return x + y if k == "add" else x - y if k == "sub" else x * y if k == "mul" else x / y
    if k == "powi":
        return _qeval(a[0], env) ** int(e.q)
    raise ValueError(k)


def _promising(th: Theory, spec) -> bool:
    """Cheap untrusted pre-filter: is h(r) = r³ f(r) smaller at aphelion than at perihelion, at the
    midpoints of the boxes (parameters at their midpoints, other positive symbols 1)? Exact: rational
    arithmetic when f is rational (so K/r³, h constant, is filtered out), else intervals, filtering out
    only what they show is not smaller. Can't tell: True, Lean decides."""
    from .enclosure import _box, ieval
    from mpmath import iv
    rsym, f, (a1, b1, a2, b2), params, positive = spec
    mid = {s: (Fraction(lo) + Fraction(hi)) / 2 for s, (lo, hi) in params.items()}
    mid.update({s: Fraction(1) for s in positive})
    x, y = (Fraction(a1) + Fraction(b1)) / 2, (Fraction(a2) + Fraction(b2)) / 2
    try:
        h = lambda r: r ** 3 * _qeval(f, {**mid, rsym: r})
        return h(y) < h(x)
    except (ValueError, KeyError, ZeroDivisionError):
        pass
    try:
        env = {s: _box(v, v) for s, v in mid.items()}
        h = lambda r: _box(r, r) ** 3 * ieval(f, {**env, rsym: _box(r, r)})
        return not h(y).a >= h(x).b
    except Exception:
        return True


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
