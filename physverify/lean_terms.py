"""Judge-side translation of theory objects into Lean statements.

This is trusted code, kept deliberately small: it serializes ASTs and rational numbers;
all meaning lives in the Lean definitions (`Expr.eval`, `Expr.dimOf`, …).
"""

from __future__ import annotations

from fractions import Fraction

from . import units
from .expr import E, to_lean
from .theory import Theory


def index(th: Theory) -> dict[str, int]:
    return {s: i for i, s in enumerate(th.symbols())}


def ctx(th: Theory) -> str:
    return "[" + ", ".join(units.lean_dim(th.dims[s]) for s in th.symbols()) + "]"


def real(q: Fraction) -> str:
    q = Fraction(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"(({q.numerator} : ℝ) / {q.denominator})"


def expr(e: E, th: Theory) -> str:
    return to_lean(e, index(th))


def law(lhs: E, rhs: E, th: Theory) -> str:
    return f"(⟨{expr(lhs, th)}, {expr(rhs, th)}⟩ : Law)"


def bound_hyps(th: Theory, bounds: dict[str, tuple[Fraction, Fraction]]) -> tuple[str, list[str]]:
    """`Bnd lo (env i) hi → …` premises for every bounded symbol, and their hypothesis names."""
    idx = index(th)
    parts, names = [], []
    for s in sorted(bounds):
        lo, hi = bounds[s]
        parts.append(f"Bnd {real(lo)} (env {idx[s]}) {real(hi)}")
        names.append(f"h_{s}")
    return " → ".join(parts), names
