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

Domain-positive variables (`positive=` in `from_expr` and `sqrt`). A caller that works on a stated
domain where some variables are > 0 (the depth h and gravity g of shallow water) may pass them as
`positive`; then sqrt(p) is also accepted when p is non-negative by form with those variables at
any exponent (e.g. sqrt(g*h)). Soundness: on the domain p >= 0, so sqrt(p) is real and
sqrt(p)^2 = p there, which is the only rule the normal form uses. Off the domain the atom means
nothing, so every result built from such an atom holds on the domain only, and the caller must
record "these variables are > 0" as a side condition of its verdict. Without `positive` nothing
changes.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

from ..expr import E, intern

Poly = dict  # {monomial: Fraction}; monomial = tuple of (atom, exponent), sorted


class Undecided(Exception):
    """The expression is outside the fragment this normal form decides."""


class _Atom(tuple):
    """A square-root atom ("s", items): a plain tuple (same equality, repr and order) that caches its
    hash and repr, which nested limiters otherwise recompute over and over."""
    def __hash__(self):
        try:
            return self._h
        except AttributeError:
            self._h = tuple.__hash__(self)
            return self._h

    def __repr__(self):
        try:
            return self._r
        except AttributeError:
            self._r = tuple.__repr__(self)
            return self._r


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
    return {((_Atom(("s", tuple(sorted(p.items(), key=_key)))), 1),): Fraction(1)}


def from_expr(e: E, sqrt_hook=None, positive=(), _memo: dict | None = None) -> Poly:
    """Normal form of e. `sqrt_hook(e, rec)`, if given, replaces the default handling of every
    sqrt node (rec normalises a subexpression with the same hook). `positive`: variables known to
    be > 0 on the caller's domain (see the module docstring); they only widen which sqrt arguments
    are accepted. Equal subtrees are normalised once per call (the result is the same)."""
    if _memo is None:
        e, _memo = intern(e), {}
    if id(e) in _memo:
        return _memo[id(e)][1]
    out = _from_expr(e, sqrt_hook, positive, _memo)
    _memo[id(e)] = (e, out)
    return out


def _from_expr(e: E, sqrt_hook, positive, _memo) -> Poly:
    rec = lambda x: from_expr(x, sqrt_hook, positive, _memo)
    k, a = e.kind, e.args
    if k == "var": return var(e.name)
    if k == "lit": return const(e.q)
    if k == "neg": return scale(rec(a[0]), -1)
    if k == "add": return add(rec(a[0]), rec(a[1]))
    if k == "sub": return add(rec(a[0]), rec(a[1]), -1)
    if k == "mul": return mul(rec(a[0]), rec(a[1]))
    if k == "div": return mul(rec(a[0]), inverse(rec(a[1])))
    if k == "powi": return power(rec(a[0]), e.q)
    if k == "sqrt" and sqrt_hook: return sqrt_hook(e, rec)
    if k == "sqrt":
        arg = rec(a[0])
        return sqrt(arg, (a[0].kind == "powi" and a[0].q % 2 == 0)
                    or bool(positive) and nonneg_by_form(arg, positive=positive))
    raise Undecided(f"{k} is outside the polynomial fragment")


def subst(p: Poly, env: dict[str, Poly], _cache: dict | None = None) -> Poly:
    """Replace variables by polynomials (re-normalizing square roots; each distinct square-root atom
    is re-normalized once per call)."""
    cache = {} if _cache is None else _cache
    out: Poly = {}
    for m, c in p.items():
        term: Poly = const(c)
        for a, k in m:
            if a[0] == "v":
                term = mul(term, power(env[a[1]], k) if a[1] in env else {_mono({a: k}): Fraction(1)})
            else:
                if a not in cache:
                    cache[a] = sqrt(subst(dict(a[1]), env, cache), nonneg=True)
                term = mul(term, power(cache[a], k))
        out = add(out, term)
    return out


def evaluate(p: Poly, env: dict[str, Fraction], _cache: dict | None = None) -> Fraction | None:
    """Exact value at a rational point, or None if a square root is irrational there (each distinct
    square-root atom is evaluated once per call)."""
    cache = {} if _cache is None else _cache
    total = Fraction(0)
    for m, c in p.items():
        for a, k in m:
            if a[0] == "v":
                c *= Fraction(env[a[1]]) ** k
                continue
            if a not in cache:
                inner = evaluate(dict(a[1]), env, cache)
                cache[a] = None if inner is None else _exact_sqrt(inner)
            r = cache[a]
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


def divide_difference(p: Poly, x: str, y: str, k: int) -> Poly | None:
    """q with p = (y - x)^k * q as an identity of normal forms, or None if there is none.

    Substitutes y = x + h and keeps p only if every monomial carries h^k explicitly; square-root
    atoms are re-normalised with their argument in terms of x and h. Then h = y - x is put back.
    """
    h = "_h"
    ph = subst(p, {y: add(var(x), var(h))})
    q: Poly = {}
    for m, c in ph.items():
        e = dict(m).get(("v", h), 0)
        if e < k:
            return None
        q = add(q, {_mono({**dict(m), ("v", h): e - k}): c})
    q = subst(q, {h: add(var(y), var(x), -1)})
    return q if not add(p, mul(power(add(var(y), var(x), -1), k), q), -1) else None


def derivative(p: Poly, x: str) -> Poly:
    """dp/dx by the power rule, for p whose square-root atoms do not involve x (on a sign cell
    every |.| has already been replaced by +-(.), so the cell polynomial qualifies)."""
    out: Poly = {}
    for m, c in p.items():
        d = dict(m)
        if any(a[0] == "s" and x in variables(dict(a[1])) for a in d):
            raise Undecided(f"derivative in {x} of a square root of an expression in {x}")
        k = d.pop(("v", x), 0)
        if k:
            out = add(out, {_mono({**d, ("v", x): k - 1}): c * k})
    return out


def nonneg_by_form(p: Poly, nonneg=(), positive=()) -> bool:
    """p >= 0 because every coefficient is positive and every factor of every monomial is >= 0:
    variables in `nonneg` (any exponent >= 0), in `positive` (any exponent), the rest only to
    even powers; square-root atoms are >= 0 by construction."""
    for m, c in p.items():
        if c <= 0:
            return False
        for a, k in m:
            if a[0] != "v" or a[1] in positive:
                continue
            if (k < 0) if a[1] in nonneg else (k % 2 != 0):
                return False
    return True


def positive_by_form(p: Poly, positive=()) -> bool:
    """p > 0 where every variable in `positive` is > 0: p is non-negative by form and at least one
    monomial is a product of `positive` variables only (no square root, which may vanish, and no
    other variable, whose even power may vanish), so that monomial is > 0 and the rest are >= 0."""
    return nonneg_by_form(p, positive=positive) and any(
        all(a[0] == "v" and a[1] in positive for a, _ in m) for m in p)


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
