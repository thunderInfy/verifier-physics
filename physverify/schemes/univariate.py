"""Exact decision of p >= 0 on an interval, for p in Q[x] (trusted, Fraction arithmetic only).

A polynomial is a list of Fraction coefficients, constant term first. The decision:

    p = c * f_1 * f_2^2 * ... * f_m^m          (square-free decomposition, Yun; f_i monic, pairwise coprime)
    g = product of the f_i with i odd          (the factors at whose roots p can change sign)

p = c * g * h^2 with h = prod f_i^(i // 2), and g, h coprime. If g has no root in the open interval
(lo, hi) (Sturm count), p has one sign on (lo, hi) away from its finitely many roots, so p >= 0 on
[lo, hi] iff p > 0 at one interior rational point (the closed interval follows by continuity; the
endpoint values are reported too). If g has a root r in (lo, hi), it is simple (g is square-free) and
h(r) != 0, so p changes sign at r: Sturm bisection isolates r between two rational points with no
other root of p between them, and p < 0 at one of them, an exact counterexample.

Sturm's theorem as used here: for square-free s with Sturm sequence s, s', -rem, ..., the number of
distinct real roots in (a, b] is V(a) - V(b), V counting sign changes with zeros dropped.
"""

from __future__ import annotations

from fractions import Fraction

MAX_STEPS = 100000          # bisection steps before giving up (never reached for a correct procedure)


# ---------------------------------------------------------------- dense polynomial arithmetic over Q

def trim(p) -> list:
    p = [Fraction(x) for x in p]
    while p and p[-1] == 0:
        p.pop()
    return p


def deg(p: list) -> int:
    return len(trim(p)) - 1          # -1 for the zero polynomial


def ev(p: list, x: Fraction) -> Fraction:
    out = Fraction(0)
    for a in reversed(p):
        out = out * x + a
    return out


def add(p: list, q: list, s=1) -> list:
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + s * (q[i] if i < len(q) else 0) for i in range(n)])


def mul(p: list, q: list) -> list:
    if not p or not q:
        return []
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def power(p: list, k: int) -> list:
    out = [Fraction(1)]
    for _ in range(k):
        out = mul(out, p)
    return out


def divmod_(p: list, q: list) -> tuple[list, list]:
    p, q = trim(p), trim(q)
    if not q:
        raise ZeroDivisionError("polynomial division by 0")
    quo = [Fraction(0)] * max(len(p) - len(q) + 1, 0)
    r = list(p)
    while len(r) >= len(q):
        c = r[-1] / q[-1]
        k = len(r) - len(q)
        quo[k] = c
        for j, b in enumerate(q):
            r[k + j] -= c * b
        r = trim(r[:-1]) if r[-1] == 0 else trim(r)
    return trim(quo), r


def monic(p: list) -> list:
    p = trim(p)
    return [a / p[-1] for a in p] if p else []


def gcd(p: list, q: list) -> list:
    p, q = trim(p), trim(q)
    while q:
        p, q = q, divmod_(p, q)[1]
    return monic(p)


def derivative(p: list) -> list:
    return trim([i * a for i, a in enumerate(p)][1:])


def show(p: list, x: str = "nu") -> str:
    terms = []
    for i, a in enumerate(trim(p)):
        if a:
            mono = x + (f"^{i}" if i > 1 else "")
            terms.append(str(a) if i == 0 else mono if a == 1 else f"-{mono}" if a == -1 else f"({a})*{mono}")
    return " + ".join(terms) or "0"


# ---------------------------------------------------------------- square-free decomposition, Sturm counts

def squarefree(p: list) -> tuple[Fraction, list]:
    """(c, [(i, f_i)]) with p = c * prod f_i^i, f_i monic, square-free, pairwise coprime, non-constant
    (Yun's algorithm over Q). p must be non-zero."""
    p = trim(p)
    if not p:
        raise ValueError("the zero polynomial has no square-free decomposition")
    c, f = p[-1], monic(p)
    out, i = [], 1
    a = gcd(f, derivative(f))
    b = divmod_(f, a)[0]
    cc = divmod_(derivative(f), a)[0]
    d = add(cc, derivative(b), -1)
    while deg(b) > 0:
        a = gcd(b, d)
        if deg(a) > 0:
            out.append((i, a))
        b = divmod_(b, a)[0]
        cc = divmod_(d, a)[0]
        d = add(cc, derivative(b), -1)
        i += 1
    recomposed = [c]
    for k, fk in out:
        recomposed = mul(recomposed, power(fk, k))
    assert recomposed == p, "square-free decomposition does not multiply back to p"
    return c, out


def sturm_sequence(s: list) -> list:
    seq = [trim(s), derivative(s)]
    while seq[-1]:
        seq.append(add([], divmod_(seq[-2], seq[-1])[1], -1))
    return seq[:-1]


def variations(seq: list, x: Fraction) -> int:
    signs = [v > 0 for v in (ev(p, x) for p in seq) if v != 0]
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def roots_open(seq: list, a: Fraction, b: Fraction) -> int:
    """Distinct roots of the square-free seq[0] in the open interval (a, b), a < b."""
    return variations(seq, a) - variations(seq, b) - (1 if ev(seq[0], b) == 0 else 0)


# ---------------------------------------------------------------- the decision

def _interior_sample(p: list, lo: Fraction, hi: Fraction) -> Fraction:
    """A rational point of (lo, hi) where p != 0: of the deg(p) + 1 points lo + (hi - lo) j/(deg + 2),
    at most deg(p) are roots."""
    n = max(deg(p), 0) + 2
    for j in range(1, n):
        x = lo + (hi - lo) * Fraction(j, n)
        if ev(p, x) != 0:
            return x
    raise AssertionError("a non-zero polynomial vanished at more points than its degree")


def _sign_change(p: list, g_seq: list, s_seq: list, lo: Fraction, hi: Fraction) -> dict:
    """Two rational points lo < x < y < hi with exactly one root of p between them, a root of g, so
    p(x) and p(y) are non-zero and of opposite signs. Bisection on Sturm counts."""
    a, b = lo, hi
    for step in range(MAX_STEPS):
        if a > lo and b < hi and ev(s_seq[0], a) != 0 and ev(s_seq[0], b) != 0 and roots_open(s_seq, a, b) == 1:
            return {"interval": [a, b], "steps": step}
        m = (a + b) / 2
        if ev(g_seq[0], m) == 0:             # a rational root of g: step off it on both sides
            d = (b - a) / 4
            while not (ev(s_seq[0], m - d) != 0 and ev(s_seq[0], m + d) != 0 and roots_open(s_seq, m - d, m + d) == 1):
                d /= 2
            return {"interval": [m - d, m + d], "steps": step, "rational_root": m}
        a, b = (a, m) if roots_open(g_seq, a, m) >= 1 else (m, b)
    raise AssertionError("Sturm bisection did not isolate a root")


def nonneg_on(p, lo, hi) -> dict:
    """Decide p >= 0 on the closed interval [lo, hi] (lo <= hi). Returns {"nonneg": bool,
    "certificate": ...} with, on False, "counterexample": {"x", "p(x)"} where p(x) < 0, lo < x < hi
    (or x = lo when lo = hi). All values are Fractions."""
    p, lo, hi = trim(p), Fraction(lo), Fraction(hi)
    if lo > hi:
        raise ValueError("empty interval")
    if not p:
        return {"nonneg": True, "certificate": {"method": "p = 0"}}
    if lo == hi:
        v = ev(p, lo)
        out = {"nonneg": v >= 0, "certificate": {"method": "single point", "p(lo)": v}}
        if v < 0:
            out["counterexample"] = {"x": lo, "p(x)": v}
        return out
    c, factors = squarefree(p)
    g = [Fraction(1)]
    s = [Fraction(1)]
    for i, f in factors:
        s = mul(s, f)
        if i % 2:
            g = mul(g, f)
    g_seq = sturm_sequence(g)
    n_g = roots_open(g_seq, lo, hi) if deg(g) > 0 else 0
    cert = {"method": "square-free decomposition + Sturm",
            "leading": c, "factors": [{"multiplicity": i, "factor": show(f)} for i, f in factors],
            "odd_part": show(g),
            "sturm_odd_part": {"V(lo)": variations(g_seq, lo), "V(hi)": variations(g_seq, hi),
                               "odd_part(hi)": ev(g, hi), "roots in (lo, hi)": n_g}}
    if n_g == 0:
        x = _interior_sample(p, lo, hi)
        v = ev(p, x)
        cert.update(sample=x, **{"p(sample)": v, "p(lo)": ev(p, lo), "p(hi)": ev(p, hi)})
        out = {"nonneg": v > 0, "certificate": cert}
        if v < 0:
            out["counterexample"] = {"x": x, "p(x)": v}
        return out
    iso = _sign_change(p, g_seq, sturm_sequence(s), lo, hi)
    x, y = iso["interval"]
    bad = x if ev(p, x) < 0 else y
    assert ev(p, bad) < 0, "p does not change sign across a simple root of its odd part"
    cert["isolation"] = iso
    return {"nonneg": False, "certificate": cert, "counterexample": {"x": bad, "p(x)": ev(p, bad)}}


def jsonable(x):
    """Fractions (also inside lists and dicts) as strings, for witnesses."""
    if isinstance(x, Fraction):
        return str(x)
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x
