"""Steps 4 + 5 — well-posedness on boxes, and validated trajectory enclosures.

Obligation `trajectory_vs_evidence`: no trajectory of the theory's dynamics that starts in the
evidence's initial box (for any parameter values in the evidence box) is inside the observed
box at time t_obs.

Planner (untrusted) searches for a certificate: a step size and one a-priori box per step.
Judge (trusted, `check_certificate`) replays it with rigorous interval arithmetic:

  for each step k, with current enclosure X_k and a-priori box B_k:
    1. well-posedness: every right-hand side is `Safe` on B_k (step 4; by
       `PhysVerify.wellPosed_exists`/`wellPosed_unique` solutions then exist and are unique)
    2. Picard inclusion: X_k + [0,h]·F(B_k) ⊆ B_k   ⇒ trajectories stay in B_k on [t, t+h]
    3. Taylor step: X_{k+1} = X_k + h·F(X_k) + h²/2 · (DF·F)(B_k)
  and finally X_n[observed] ∩ observed bounds = ∅, with every B_k inside the theory's regime.

Guarantee: VALIDATED (not a Lean proof): it trusts mpmath's outward-rounded interval
arithmetic and this file's ~100-line checker.
"""

from __future__ import annotations

from fractions import Fraction

from mpmath import iv, mpf

from ..core import VALIDATED, Candidate
from ..expr import E, diff, parse, simplify, variables
from ..theory import Evidence, Theory
from .binding import bind

NAME = "enclosure"
iv.prec = 64  # outward rounded; rigour does not depend on precision, only tightness


# ------------------------------------------------------------------ trusted interval kernel

class Unsafe(Exception):
    """A box where the vector field may not be C¹ (step-4 contract fails): no conclusion."""


def _ivq(q) -> iv.mpf:
    q = Fraction(q)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def ieval(e: E, env: dict[str, iv.mpf]) -> iv.mpf:
    """Interval evaluation that also enforces `Expr.Safe` on the whole box."""
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return _ivq(e.q)
    if k == "pi": return iv.pi
    if k == "neg": return -ieval(a[0], env)
    x = ieval(a[0], env)
    if k in ("add", "sub", "mul", "div"):
        y = ieval(a[1], env)
        if k == "add": return x + y
        if k == "sub": return x - y
        if k == "mul": return x * y
        if 0 in y: raise Unsafe(f"denominator may vanish in {e!r}")
        return x / y
    if k == "powi":
        if e.q < 0 and 0 in x: raise Unsafe(f"negative power of possibly zero base in {e!r}")
        return x ** int(e.q)
    if k in ("sqrt", "rpow"):
        if x.a <= 0: raise Unsafe(f"{k} of possibly non-positive argument in {e!r}")
        return iv.sqrt(x) if k == "sqrt" else iv.exp(_ivq(e.q) * iv.log(x))
    if k == "app":
        if e.name == "log" and x.a <= 0: raise Unsafe(f"log of possibly non-positive argument")
        return {"sin": iv.sin, "cos": iv.cos, "exp": iv.exp, "log": iv.log}[e.name](x)
    raise ValueError(k)


def _box(lo, hi) -> iv.mpf:
    """Smallest representable interval containing [lo, hi] (rationals)."""
    return iv.mpf([_ivq(lo).a, _ivq(hi).b])


def _endpoints(x: iv.mpf) -> tuple[str, str]:
    """Exact rational endpoints of an interval (for certificates)."""
    def frac(t):
        sign, man, exp, _ = t
        f = Fraction(man) * (Fraction(2) ** exp)
        return -f if sign else f
    lo, hi = x._mpi_
    return str(frac(lo)), str(frac(hi))


def _hull(x: iv.mpf, y: iv.mpf) -> iv.mpf:
    return iv.mpf([min(x.a, y.a), max(x.b, y.b)])


def _subset(x: iv.mpf, y: iv.mpf) -> bool:
    return y.a <= x.a and x.b <= y.b


class System:
    def __init__(self, th: Theory):
        self.t, self.rhs = th.dynamics
        self.vars = list(self.rhs)
        # second derivative x'' = DF · F, symbolically
        self.acc = {}
        for v in self.vars:
            terms = [E("mul", (diff(self.rhs[v], u), self.rhs[u])) for u in self.vars]
            acc = terms[0]
            for t in terms[1:]:
                acc = E("add", (acc, t))
            self.acc[v] = simplify(acc)

    def F(self, X, P):  return {v: ieval(self.rhs[v], {**P, **X}) for v in self.vars}
    def A(self, X, P):  return {v: ieval(self.acc[v], {**P, **X}) for v in self.vars}


def replay(sys_: System, X0, P, h: Fraction, boxes, regime) -> dict:
    """The trusted checker. Returns the final enclosure; raises on any failed condition."""
    H = _ivq(h)
    Hs = iv.mpf([0, 1]) * H
    X = dict(X0)
    for Braw in boxes:
        B = {v: _box(Fraction(Braw[v][0]), Fraction(Braw[v][1])) for v in sys_.vars}
        for v, (lo, hi) in regime.items():
            if v in B and not _subset(B[v], _box(lo, hi)):
                raise Unsafe(f"enclosure leaves the theory's regime in {v}")
        FB = sys_.F(B, P)                                     # also checks Safe on B (step 4)
        for v in sys_.vars:
            if not _subset(X[v] + Hs * FB[v], B[v]):
                raise Unsafe("Picard inclusion fails")
        FX, AB = sys_.F(X, P), sys_.A(B, P)
        X = {v: X[v] + H * FX[v] + (H * H / 2) * AB[v] for v in sys_.vars}
    return X


# ------------------------------------------------------------------ evidence plumbing

def _setup(th: Theory, ev: Evidence):
    tr = ev.extra.get("trajectory")
    if not tr or not th.dynamics:
        return None
    sys_ = System(th)
    params = {s: b for s, b in bind(th, ev).items() if s not in sys_.vars}
    P = {s: _box(lo, hi) for s, (lo, hi) in params.items()}
    X0 = {v: _box(*ev.bounds[q]) for v, q in tr["initial"].items()}
    obs = {v: ev.bounds[q] for v, q in tr["observe"].items()}
    t_obs = Fraction(str(tr["t_obs"]))
    if set(X0) != set(sys_.vars):
        return None
    used = set().union(*(variables(e) for e in sys_.rhs.values()))
    missing = used - set(params) - set(sys_.vars)
    if missing:
        return None  # unbounded parameter: v1 cannot enclose
    return sys_, P, X0, obs, t_obs


def obligation(args, th: Theory, evidence: dict[str, Evidence]):
    from ..obligations import Obligation
    ev = evidence[args["evidence"]]
    if _setup(th, ev) is None:
        raise KeyError("no dynamics/trajectory or unbounded parameters")
    tr = ev.extra["trajectory"]
    for v, q in tr["initial"].items():
        if v in th.regime:
            (lo, hi), (rlo, rhi) = ev.bounds[q], th.regime[v]
            if lo < rlo or hi > rhi:
                return Obligation(f"initial {v} ∈ [{float(lo):.4g}, {float(hi):.4g}] is outside the "
                                  f"theory's regime [{float(rlo):.4g}, {float(rhi):.4g}]",
                                  "", [], [ev.id], skip="OUT_OF_REGIME")
    return Obligation(
        claim=(f"no trajectory from {ev.id}'s initial box is inside the observed box "
               f"{tr['observe']} at t = {tr['t_obs']}"),
        guarantee=VALIDATED,
        assumptions=[f"hard bounds of {ev.id} contain the true values ({ev.source})",
                     "well-posedness: Safe on every step box ⇒ unique solutions "
                     "(PhysVerify.wellPosed_exists / wellPosed_unique)",
                     "mpmath interval arithmetic is correctly outward-rounded"],
        evidence=[ev.id],
        numeric={"theory": th, "evidence": ev},
    )


def check_certificate(numeric: dict, cert) -> tuple[bool, str]:
    th, ev = numeric["theory"], numeric["evidence"]
    sys_, P, X0, obs, t_obs = _setup(th, ev)
    try:
        h = Fraction(cert["h"])
        boxes = cert["boxes"]
        if h <= 0 or h * len(boxes) != t_obs:
            return False, "steps do not reach t_obs exactly"
        X = replay(sys_, X0, P, h, boxes, th.regime)
    except (Unsafe, KeyError, TypeError, ValueError) as ex:
        return False, f"certificate failed: {ex}"
    for v, (lo, hi) in obs.items():
        o = _box(lo, hi)
        if X[v].b < o.a or o.b < X[v].a:
            return True, (f"replayed {len(boxes)} steps: {v}(t_obs) ∈ [{float(X[v].a):.6g}, "
                          f"{float(X[v].b):.6g}], observed [{float(lo):.6g}, {float(hi):.6g}]")
    return False, "enclosure overlaps the observation (no conclusion)"


# ------------------------------------------------------------------ untrusted planner

def _search(sys_: System, X0, P, h: Fraction, n: int, regime):
    H = _ivq(h)
    Hs = iv.mpf([0, 1]) * H
    X, boxes = dict(X0), []
    for _ in range(n):
        FX = sys_.F(X, P)
        B = {v: X[v] + Hs * FX[v] for v in sys_.vars}
        for _ in range(40):  # Picard iteration with epsilon-inflation
            FB = sys_.F(B, P)
            nxt = {v: X[v] + Hs * FB[v] for v in sys_.vars}
            if all(_subset(nxt[v], B[v]) for v in sys_.vars):
                break
            B = {v: _hull(B[v], nxt[v]) for v in sys_.vars}
            B = {v: B[v] + (B[v] - B[v].mid) * mpf("0.05")
                 + iv.mpf([-1, 1]) * (abs(B[v].mid) * mpf("1e-15") + mpf("1e-300")) for v in sys_.vars}
        else:
            return None
        boxes.append({v: _endpoints(B[v]) for v in sys_.vars})
        AB = sys_.A(B, P)
        X = {v: X[v] + H * FX[v] + (H * H / 2) * AB[v] for v in sys_.vars}
    return boxes


def propose(th: Theory, evidence: list[Evidence]) -> list[Candidate]:
    out = []
    for ev in evidence:
        st = _setup(th, ev)
        if st is None:
            continue
        sys_, P, X0, obs, t_obs = st
        if any(not _subset(X0[v], _box(*th.regime[v])) for v in X0 if v in th.regime):
            # let the judge record that the theory makes no claim here
            out.append(Candidate(NAME, "trajectory_vs_evidence", {"evidence": ev.id}, None))
            continue
        for n in (200, 800):
            h = t_obs / n
            try:
                boxes = _search(sys_, X0, P, h, n, th.regime)
            except Unsafe:
                boxes = None
            if boxes is None:
                continue
            cert = {"h": str(h), "boxes": boxes}
            ok, _ = check_certificate({"theory": th, "evidence": ev}, cert)
            if ok:
                out.append(Candidate(NAME, "trajectory_vs_evidence", {"evidence": ev.id}, cert,
                                     note=f"{n} Taylor-2 steps"))
                break
    return out


__all__ = ["ieval", "Unsafe", "System", "replay", "check_certificate", "obligation", "propose", "parse"]
