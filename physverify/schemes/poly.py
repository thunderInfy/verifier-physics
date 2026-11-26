"""Exact normal form for the expressions that numerical fluxes use.

A `Poly` is a Laurent polynomial over Q whose atoms are variables and square roots
`sqrt(p)` of polynomials that are obviously non-negative (every monomial has a positive
coefficient and even exponents; so sqrt(u^2) = |u| is allowed). The only rewrite rule
beyond ring arithmetic is sqrt(p)^2 = p, which holds because p >= 0.

Two expressions with the same normal form are equal wherever every denominator is
non-zero. Different normal forms do NOT prove the expressions differ (the atoms may be
related, e.g. sqrt(u^4) and u^2); callers must then find an exact counterexample point.
sqrt(q^2k) is also accepted for any q, since a syntactic even power is non-negative. Anything outside this fragment (pi, sin, non-integer powers, division by a sum) raises
`Undecided`.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

from ..expr import E

Poly = dict  # {monomial: Fraction}; monomial = tuple of (atom, exponent), sorted


class Undecided(Exception):
    """The expression is outside the fragment this normal form decides."""


def _key(x) -> str:
    return repr(x)


def _mono(pairs: dict) -> tuple:
    return tuple(sorted(((a, k) for a, k in pairs.items() if k != 0), key=_key))


def const(q) -> Poly:
    q = Fraction(q)
    return {(): q} if q else {}


def var(name: str) -> Poly:
    return {((("v", name), 1),): Fraction(1)}


def add(p: Poly, q: Poly, sign: int = 1) -> Poly:
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + sign * c
        if not out[m]:
            del out[m]
    return out


def scale(p: Poly, c) -> Poly:
    return {m: v * c for m, v in p.items()} if c else {}


def _mono_mul(m1: tuple, m2: tuple) -> Poly:
    pairs: dict = dict(m1)
    for a, k in m2:
        pairs[a] = pairs.get(a, 0) + k
    out: Poly = {(): Fraction(1)}
    for a, k in pairs.items():
        if a[0] == "s" and k >= 2:  # sqrt(p)^k = sqrt(p)^(k mod 2) * p^(k div 2)
            out = mul(out, power(dict(a[1]), k // 2))
            pairs[a] = k % 2
    rest = {_mono(pairs): Fraction(1)}
    return rest if out == {(): Fraction(1)} else mul(out, rest)


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            out = add(out, scale(_mono_mul(m1, m2), c1 * c2))
    return out


def power(p: Poly, n: int) -> Poly:
    if n < 0:
        return power(inverse(p), -n)
    out: Poly = {(): Fraction(1)}
    for _ in range(n):
        out = mul(out, p)
    return out


def inverse(p: Poly) -> Poly:
    """1/p, only for a single monomial over plain variables (assumed non-zero)."""
    if len(p) != 1:
        raise Undecided("division by a sum is outside the polynomial fragment")
    ((m, c),) = p.items()
    if any(a[0] != "v" for a, _ in m):
        raise Undecided("division by a square root")
    return {_mono({a: -k for a, k in m}): 1 / c}


def _obviously_nonneg(p: Poly) -> bool:
    return all(c > 0 and all(k % 2 == 0 for a, k in m if a[0] == "v") for m, c in p.items())


def _exact_sqrt(q: Fraction) -> Fraction | None:
    n, d = isqrt(q.numerator), isqrt(q.denominator)
    return Fraction(n, d) if n * n == q.numerator and d * d == q.denominator else None


def sqrt(p: Poly, nonneg: bool = False) -> Poly:
    """sqrt(p); `nonneg` says p >= 0 is already known (a syntactic square, or a substitution
    instance of an atom already shown non-negative everywhere)."""
    if not p:
        return {}
    if set(p) == {()} and p[()] > 0 and _exact_sqrt(p[()]) is not None:
        return const(_exact_sqrt(p[()]))
    if not (nonneg or _obviously_nonneg(p)):
        raise Undecided(f"cannot show sqrt argument {show(p)} is non-negative")
    return {((("s", tuple(sorted(p.items(), key=_key))), 1),): Fraction(1)}


def from_expr(e: E) -> Poly:
    k, a = e.kind, e.args
    if k == "var": return var(e.name)
    if k == "lit": return const(e.q)
    if k == "neg": return scale(from_expr(a[0]), -1)
    if k == "add": return add(from_expr(a[0]), from_expr(a[1]))
    if k == "sub": return add(from_expr(a[0]), from_expr(a[1]), -1)
    if k == "mul": return mul(from_expr(a[0]), from_expr(a[1]))
    if k == "div": return mul(from_expr(a[0]), inverse(from_expr(a[1])))
    if k == "powi": return power(from_expr(a[0]), e.q)
    if k == "sqrt": return sqrt(from_expr(a[0]), a[0].kind == "powi" and a[0].q % 2 == 0)
    raise Undecided(f"{k} is outside the polynomial fragment")


def subst(p: Poly, env: dict[str, Poly]) -> Poly:
    """Replace variables by polynomials (re-normalizing square roots)."""
    out: Poly = {}
    for m, c in p.items():
        term: Poly = const(c)
        for a, k in m:
            if a[0] == "v":
                term = mul(term, power(env[a[1]], k) if a[1] in env else {_mono({a: k}): Fraction(1)})
            else:
                term = mul(term, power(sqrt(subst(dict(a[1]), env), nonneg=True), k))
        out = add(out, term)
    return out


def evaluate(p: Poly, env: dict[str, Fraction]) -> Fraction | None:
    """Exact value at a rational point, or None if a square root is irrational there."""
    total = Fraction(0)
    for m, c in p.items():
        for a, k in m:
            if a[0] == "v":
                c *= Fraction(env[a[1]]) ** k
                continue
            inner = evaluate(dict(a[1]), env)
            r = None if inner is None else _exact_sqrt(inner)
            if r is None:
                return None
            c *= r ** k
        total += c
    return total


def variables(p: Poly) -> set[str]:
    out: set[str] = set()
    for m in p:
        for a, _ in m:
            out |= {a[1]} if a[0] == "v" else variables(dict(a[1]))
    return out


def show(p: Poly) -> str:
    if not p:
        return "0"
    terms = []
    for m, c in sorted(p.items(), key=lambda mc: _key(mc[0])):
        factors = [(a[1] if a[0] == "v" else f"sqrt({show(dict(a[1]))})") + (f"^{k}" if k != 1 else "")
                   for a, k in m]
        head = [] if c == 1 and factors else ["-"] if c == -1 and factors else [str(c)]
        terms.append("".join(head) + ("*" if head != ["-"] and head and factors else "") + "*".join(factors))
    return " + ".join(terms).replace("+ -", "- ")
