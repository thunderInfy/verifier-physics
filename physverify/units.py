"""Dimensions as integer exponent vectors over the 7 SI base dimensions.

Order matches `PhysVerify.Dim` (Fin 7 → ℤ): L M T I Θ N J.
Python computes dimensions only to *plan*; the Lean kernel re-derives them.
"""

from __future__ import annotations

from fractions import Fraction

from .expr import E

BASES = ("L", "M", "T", "I", "Th", "N", "J")
Dim = tuple[int, ...]
ZERO: Dim = (0,) * 7


def parse_dim(s: str) -> Dim:
    """'L^3 M^-1 T^-2' -> (3,-1,-2,0,0,0,0); '1' or '' -> dimensionless."""
    d = [0] * 7
    s = s.strip()
    if s in ("", "1"):
        return ZERO
    for part in s.split():
        base, _, exp = part.partition("^")
        if base not in BASES:
            raise ValueError(f"unknown base dimension {base!r} (use {BASES})")
        d[BASES.index(base)] += int(exp) if exp else 1
    return tuple(d)


def fmt_dim(d: Dim) -> str:
    parts = [f"{b}^{x}" if x != 1 else b for b, x in zip(BASES, d) if x]
    return " ".join(parts) or "1"


def add(a: Dim, b: Dim) -> Dim: return tuple(x + y for x, y in zip(a, b))
def sub(a: Dim, b: Dim) -> Dim: return tuple(x - y for x, y in zip(a, b))
def smul(n: int, a: Dim) -> Dim: return tuple(n * x for x in a)


class DimError(ValueError):
    pass


def dim_of(e: E, ctx: dict[str, Dim]) -> Dim:
    """Mirror of `Expr.dimOf`; raises DimError where Lean would return `none`."""
    k, a = e.kind, e.args
    if k == "var":
        if e.name not in ctx:
            raise DimError(f"undeclared symbol {e.name!r}")
        return ctx[e.name]
    if k in ("lit", "pi"):
        return ZERO
    if k == "neg":
        return dim_of(a[0], ctx)
    if k in ("add", "sub"):
        x, y = dim_of(a[0], ctx), dim_of(a[1], ctx)
        if x != y:
            raise DimError(f"{k} of {fmt_dim(x)} and {fmt_dim(y)} in {e!r}")
        return x
    if k == "mul":
        return add(dim_of(a[0], ctx), dim_of(a[1], ctx))
    if k == "div":
        return sub(dim_of(a[0], ctx), dim_of(a[1], ctx))
    if k == "powi":
        return smul(e.q, dim_of(a[0], ctx))
    if k == "sqrt":
        x = dim_of(a[0], ctx)
        if any(v % 2 for v in x):
            raise DimError(f"sqrt of {fmt_dim(x)} (odd exponent) in {e!r}")
        return tuple(v // 2 for v in x)
    if k in ("rpow", "app"):
        x = dim_of(a[0], ctx)
        if x != ZERO:
            what = f"^{e.q}" if k == "rpow" else e.name
            raise DimError(f"{what} needs a dimensionless argument, got {fmt_dim(x)} in {e!r}")
        return ZERO
    raise ValueError(k)


def lean_dim(d: Dim) -> str:
    return "![" + ", ".join(str(x) for x in d) + "]"


__all__ = ["Dim", "ZERO", "parse_dim", "fmt_dim", "dim_of", "DimError", "lean_dim", "Fraction"]
