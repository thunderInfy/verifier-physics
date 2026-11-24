"""Step 3 — algebraic contradiction certificates (law vs. hard-bound evidence).

Obligation `law_vs_evidence`: for every state inside the evidence box, the law fails.
Untrusted planning: evaluate both sides of the law in exact rational interval arithmetic;
if the intervals are disjoint, emit a Lean proof that rebuilds those bounds node by node
with the `Bnd.*` lemmas (each step's numeric side conditions closed by `norm_num`).
"""

from __future__ import annotations

import math
from fractions import Fraction

from ..core import Candidate
from ..expr import E, to_lean
from ..lean_terms import index, real
from ..theory import Evidence, Theory
from .binding import bind

NAME = "algebra"
SIG = 15  # significant digits kept when rounding bounds outward
PI_LO, PI_HI = Fraction("3.141592"), Fraction("3.141593")


def _round(x: Fraction, up: bool) -> Fraction:
    if x == 0:
        return x
    e = math.floor(math.log10(abs(float(x))))
    scale = Fraction(10) ** (SIG - 1 - e)
    y = x * scale
    return Fraction(math.ceil(y) if up else math.floor(y)) / scale


def _sqrt_bounds(lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    L = _round(Fraction(math.sqrt(float(lo))), up=False)
    while L * L > lo:
        L = _round(L * Fraction(999999, 1000000), up=False)
    U = _round(Fraction(math.sqrt(float(hi))), up=True)
    while U * U < hi:
        U = _round(U * Fraction(1000001, 1000000), up=True)
    return L, U


class _Chain:
    """Builds `have` steps; returns (step name, lo, hi) per node, or raises Unsupported."""

    class Unsupported(Exception):
        pass

    def __init__(self, th: Theory, bounds: dict[str, tuple[Fraction, Fraction]]):
        self.idx, self.bounds, self.lines, self.n = index(th), bounds, [], 0

    def _emit(self, rhs: str, lo: Fraction, hi: Fraction) -> tuple[str, Fraction, Fraction]:
        lo, hi = _round(lo, up=False), _round(hi, up=True)
        self.n += 1
        name = f"s{self.n}"
        self.lines.append(f"have {name} := {rhs.format(L=real(lo), U=real(hi))}")
        return name, lo, hi

    def node(self, e: E):
        k, a = e.kind, e.args
        side = "(by norm_num)"
        if k == "var":
            if e.name not in self.bounds:
                raise self.Unsupported(f"{e.name} unbounded")
            lo, hi = self.bounds[e.name]
            self.n += 1
            name = f"s{self.n}"
            self.lines.append(f"have {name} := Bnd.var (env := env) (i := {self.idx[e.name]}) h_{e.name}")
            return name, lo, hi
        if k == "lit":
            q = Fraction(e.q)
            q_lean = to_lean(e, self.idx)[len("(.lit "):-1]
            return self._emit(f"Bnd.lit (env := env) {q_lean} (L := {{L}}) (U := {{U}}) {side} {side}", q, q)
        if k == "pi":
            return self._emit(f"Bnd.pi (env := env) (L := {{L}}) (U := {{U}}) {side} {side}", PI_LO, PI_HI)
        if k == "neg":
            s, lo, hi = self.node(a[0])
            return self._emit(f"Bnd.neg {s} (L := {{L}}) (U := {{U}}) {side} {side}", -hi, -lo)
        if k in ("add", "sub", "mul", "div"):
            (s1, l1, h1), (s2, l2, h2) = self.node(a[0]), self.node(a[1])
            if k == "add":
                lo, hi, extra = l1 + l2, h1 + h2, ""
            elif k == "sub":
                lo, hi, extra = l1 - h2, h1 - l2, ""
            elif k == "mul":
                if l1 < 0 or l2 < 0:
                    raise self.Unsupported("mul of possibly negative factor")
                lo, hi, extra = l1 * l2, h1 * h2, f" {side} {side}"
            else:
                if l1 < 0 or l2 <= 0:
                    raise self.Unsupported("div needs non-negative numerator, positive denominator")
                lo, hi, extra = l1 / h2, h1 / l2, f" {side} {side}"
            return self._emit(f"Bnd.{k} {s1} {s2}{extra} (L := {{L}}) (U := {{U}}) {side} {side}", lo, hi)
        if k == "powi":
            s, l, h = self.node(a[0])
            n = e.q
            if n >= 0:
                if l < 0:
                    raise self.Unsupported("power of possibly negative base")
                return self._emit(f"Bnd.powi_nonneg {s} {side} {side} (n := {n}) (L := {{L}}) (U := {{U}}) {side} {side}",
                                  l ** n, h ** n)
            if l <= 0:
                raise self.Unsupported("negative power of possibly non-positive base")
            return self._emit(f"Bnd.powi_neg {s} {side} {side} (n := ({n})) (L := {{L}}) (U := {{U}}) {side} {side}",
                              h ** n, l ** n)
        if k == "sqrt":
            s, l, h = self.node(a[0])
            if l < 0:
                raise self.Unsupported("sqrt of possibly negative")
            lo, hi = _sqrt_bounds(l, h)
            self.n += 1
            name = f"s{self.n}"
            self.lines.append(f"have {name} := Bnd.sqrt {s} (L := {real(lo)}) (U := {real(hi)}) "
                              f"{side} {side} {side} {side}")
            return name, lo, hi
        raise self.Unsupported(f"{k} not supported by interval certificates")


def certificate(th: Theory, law, bounds) -> tuple[str, Fraction, Fraction, Fraction, Fraction] | None:
    """Lean tactic proof of the obligation, or None if the intervals overlap / unsupported."""
    ch = _Chain(th, bounds)
    try:
        sl, ll, hl = ch.node(law.lhs)
        sr, lr, hr = ch.node(law.rhs)
    except _Chain.Unsupported:
        return None
    if not (hl < lr or hr < ll):
        return None
    hyps = " ".join(f"h_{s}" for s in sorted(bounds))
    proof = "\n".join([f"intro env {hyps} hlaw", *ch.lines,
                       f"exact Bnd.disjoint {sl} {sr} hlaw (by norm_num)"])
    return proof, ll, hl, lr, hr


def propose(th: Theory, evidence: list[Evidence]) -> list[Candidate]:
    out = []
    for ev in evidence:
        bounds = bind(th, ev)
        for law in th.laws:
            cert = certificate(th, law, bounds)
            if cert:
                proof, ll, hl, lr, hr = cert
                out.append(Candidate(NAME, "law_vs_evidence", {"law": law.name, "evidence": ev.id},
                                     proof, note=f"lhs ∈ [{float(ll):.6g}, {float(hl):.6g}], "
                                                 f"rhs ∈ [{float(lr):.6g}, {float(hr):.6g}]"))
    return out
