"""Harten's incremental form with general C, D for limited schemes of linear advection (trusted, exact).

`limiters.tvd_harten` certifies Harten's lemma on the sign cells of the five-point update with the upwind
split (C = 0). This module certifies it with general coefficients, read off the numerical flux, for a
class of flux-limited schemes; `limiters.tvd_harten` runs both and reports VERIFIED if either holds.

Scope (each item checked exactly, else `OutOfScope`, which is UNKNOWN). The PDE is u_t + a u_x = 0
with a > 0, and the spec declares a numerical flux F(uLL, uL, uR) on the three-point window of its
interface (uRR unused). Write p = uL - uLL (the upwind difference) and q = uR - uL (the interface's own
difference). G = F - a*uL is split into sign cells (`interface_cells`: every |x| = sqrt(x^2), x a
quotient N/D of polynomials, by the closed signs of N and of D; a cell is dropped only with a Farkas
certificate that it is lower-dimensional, as in `limiters.cells`, so the retained cells cover the
space). On each cell G = N/D with D free of lam, and we require: the cell atoms are linear forms in
p, q (so every cell is a cone in (p, q), the same for every uL); D is homogeneous of some degree k in
p, q and N = sum_m lam^m N_m with each N_m homogeneous of degree k + 1, none of them involving uL.
Then G is translation invariant and positively homogeneous of degree 1, on every cell and so
everywhere (where D != 0). We also require G = alpha(lam) q + beta(lam) L(p, q) with alpha, beta
Laurent polynomials in lam and one lam-free limited slope L for every cell (alpha from G at
(p, q) = (0, 1); L and beta from the rest, which must have rank one over the powers of lam). Sweby's
form F = a uL + (a/2)(1 - nu) L has alpha = 0; a centred linear scheme F = a (uL + uR)/2 -
Q(nu)/(2 lam) (uR - uL) has beta = 0; van Leer's limiter makes L rational.

With nu = a*lam, A(nu) = lam*alpha and B(nu) = lam*beta are polynomials in nu, and by homogeneity
    lam*G / q = A + B*phi,   phi = L/q, a function of r = p/q (and of the sign of q),
    lam*G / p = A*rho + B*xi, xi = L/p, a function of rho = q/p (and of the sign of p).
On the lines (p, q) = (r, 1), (-r, -1) and (1, rho), (-1, -rho) the cells cut intervals on which phi
and xi are rational functions of one variable; `ranges` computes their exact infimum and supremum
over each line, per sign: values at the interval ends, limits at infinity, and at the critical points,
which must be rational (rational-root search, then a Sturm count that no other critical point lies in
the interval; otherwise OutOfScope). Every value in a range is taken (or approached) by some state, and
values at different interfaces are independent (r_{i-1} and rho_i depend on different differences).

The update is H = u_i - lam (F_{i+1/2} - F_{i-1/2}), so N = H - u_i = -nu Delta_{i-1/2} - lam (G_{i+1/2}
- G_{i-1/2}). Two splits into Harten's form N = C_i Delta_{i+1/2} - D_{i-1} Delta_{i-1/2} (Lean's
convention: C_i is C_{i+1/2}, D_{i-1} is D_{i-1/2}; the bound is C_j + D_j <= 1):
- upwind: C = 0, D_{i-1} = nu + lam (G_{i+1/2} - G_{i-1/2}) / Delta_{i-1/2}, needs alpha = 0; with
  s the sign of Delta_{i-1/2}: D = nu + B (xi_s(rho_i) - phi_s(r_{i-1})). Conditions: 0 <= D <= 1.
- flux: C_i = -lam G_{i+1/2} / Delta_{i+1/2} = -(A + B phi(r_i)), D_{i-1} = nu - A - B phi(r_{i-1}),
  the split of `Harten.fluxC` / `fluxD`. Conditions: C >= 0, D >= 0, C_j + D_j = nu - 2A - 2B phi(r_j)
  <= 1, and also C_i + D_{i-1} <= 1 over independent phi(r_i), phi(r_{i-1}), so that u_i^{n+1} =
  (1 - C_i - D_{i-1}) u_i + C_i u_{i+1} + D_{i-1} u_{i-1} is a convex combination (the maximum-principle
  row of claims.py rests on it; with C = 0 that is D <= 1, already a condition).
Each condition is c0(nu) + sum_k c_k(nu) v_k >= 0 with the v_k independent, each over its range: for
fixed nu it is affine in v, so its minimum over a box is at a corner, and over a ray it is bounded
below iff c_k has the right sign. `decide` checks exactly that: the sign of c_k on [lo, hi] for an
unbounded range, then every corner polynomial >= 0 on [lo, hi] (`univariate.nonneg_on`: square-free
decomposition and Sturm). So the conditions are decided exactly, both ways, given the split; Harten's
form is not unique, so a failure decides nothing.

The difference-zero cases are identities, never a division: where Delta = 0 the quotient in C or D is
a free choice (Lean's x/0 = 0), and the form needs the numerator to vanish there. G(p, 0) = 0 (the
own difference zero) for both splits, and G(0, q) = 0 (the upwind difference zero) for the upwind
split, checked at (p, q) = (+-1, 0) and (0, +-1) on a cell containing the point (by homogeneity that
is every point of those lines). With them, C_i Delta_{i+1/2} - D_{i-1} Delta_{i-1/2} = N for every
state, Delta = 0 included. The bounds hold at the states where a quotient is set to 0 as well: C, D >= 0
there trivially, and C_j <= 1, D_j <= 1 follow from C_j + D_j <= 1 and C, D >= 0 at the other states.
A rational limiter's denominator vanishes only where both differences do (van Leer: |p| + |q|); there
G is 0/0, and we take the value 0, its limit (the scheme's own expression is undefined there).
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product

from ..expr import E, intern, lit, var, variables
from . import checks, poly as P, univariate as U

PV, QV = "_p", "_q"      # p = uL - uLL, q = uR - uL

# the lines on which phi = L/q and xi = L/p are read: point(t) = base + t*direction, value = sign*L
FAMILIES = {"phi+": ((0, 1), (1, 0), 1), "phi-": ((0, -1), (-1, 0), -1),
            "xi+": ((1, 0), (0, 1), 1), "xi-": ((-1, 0), (0, -1), -1)}


class OutOfScope(P.Undecided):
    """The scheme is outside the class this certificate covers (UNKNOWN, not a verdict)."""


def _lin2(p: P.Poly) -> tuple | None:
    """(c_p, c_q) for a linear form c_p p + c_q q (no constant, no other variable), else None."""
    got = checks._linear(p, [PV, QV])
    if got is None or got[0]:
        return None
    return got[1].get(PV, Fraction(0)), got[1].get(QV, Fraction(0))


def _lam_parts(p: P.Poly) -> dict:
    """{m: Poly free of lam} with p = sum_m lam^m p_m (m may be negative)."""
    out: dict = {}
    for mono, c in p.items():
        d = dict(mono)
        k = d.pop(("v", "lam"), 0)
        out[k] = P.add(out.get(k, {}), {P._mono(d): c})
    return out


def _split_key(x: P.Poly) -> tuple:
    """x scaled to the representative its sign split is keyed by (x and 2x share one split), and the
    factor g > 0 with x = g * representative."""
    g = abs(min(x.items(), key=lambda mc: P._key(mc[0]))[1])
    return P.scale(x, 1 / g), g


def _sign(x: P.Poly, assign: dict) -> int:
    """The sign the cell gives x (+1 for x >= 0, -1 for x <= 0, 0 for x = 0), or raise a split on x."""
    if set(x) <= {()}:
        v = x.get((), Fraction(0))
        return (v > 0) - (v < 0)
    y, _ = _split_key(x)
    for key, s in ((checks._key(y), 1), (checks._key(P.scale(y, -1)), -1)):
        if key in assign:
            return s * assign[key][1]
    raise checks._Split(y)


def _rational(e: E, assign: dict, memo: dict) -> tuple:
    """(N, D) with e = N/D on the cell `assign` (polynomials; |x| for x = n/d is (sgn n) n / ((sgn d) d)).
    Raises checks._Split for a sign the cell does not fix, Undecided outside the fragment."""
    if id(e) in memo:
        return memo[id(e)][1]
    k, a = e.kind, e.args
    rec = lambda x: _rational(x, assign, memo)
    one = P.const(1)
    if k == "var":
        out = (P.var(e.name), one)
    elif k == "lit":
        out = (P.const(e.q), one)
    elif k == "neg":
        n, d = rec(a[0])
        out = (P.scale(n, -1), d)
    elif k in ("add", "sub"):
        (n1, d1), (n2, d2) = rec(a[0]), rec(a[1])
        out = (P.add(P.mul(n1, d2), P.mul(n2, d1), 1 if k == "add" else -1), P.mul(d1, d2)) if d1 != d2 else \
            (P.add(n1, n2, 1 if k == "add" else -1), d1)
    elif k == "mul":
        (n1, d1), (n2, d2) = rec(a[0]), rec(a[1])
        out = (P.mul(n1, n2), P.mul(d1, d2))
    elif k == "div":
        (n1, d1), (n2, d2) = rec(a[0]), rec(a[1])
        if not n2:
            raise P.Undecided("division by 0")
        out = (P.mul(n1, d2), P.mul(d1, n2))
    elif k == "powi":
        n, d = rec(a[0])
        out = (P.power(n, e.q), P.power(d, e.q)) if e.q >= 0 else (P.power(d, -e.q), P.power(n, -e.q))
    elif k == "sqrt":
        x = a[0]
        if x.kind != "powi" or x.q % 2:
            raise P.Undecided("square root of something other than an even power")
        n, d = rec(x.args[0])
        n, d = P.power(n, x.q // 2), P.power(d, x.q // 2)
        sn, sd = _sign(n, assign), _sign(d, assign)
        if sd == 0:
            raise P.Undecided("a denominator vanishes identically on a sign cell")
        out = (P.scale(n, sn), P.scale(d, sd))
    else:
        raise P.Undecided(f"{k} is outside the rational fragment")
    memo[id(e)] = (e, out)
    return out


def _cells(G: E) -> tuple[list, int, int]:
    """Retained sign cells of G as [(N, D, atoms)], the number explored and the number pruned (see the
    module docstring and `limiters._cells`)."""
    from . import limiters
    G = intern(G)
    todo, out, explored, pruned = [{}], [], 0, 0
    while todo:
        assign = todo.pop()
        explored += 1
        if explored > limiters.MAX_CELLS:
            raise limiters.TooMany(f"more than {limiters.MAX_CELLS} sign cells explored; giving up (UNKNOWN, not a verdict)")
        try:
            n, d = _rational(G, assign, {})
        except checks._Split as s:
            for sgn in (1, -1):
                a2 = {**assign, checks._key(s.p): (s.p, sgn)}
                if limiters.lower_dimensional([P.scale(x, sg) for x, sg in a2.values()]):
                    pruned += 1
                else:
                    todo.append(a2)
            continue
        out.append((n, d, [P.scale(x, sg) for x, sg in assign.values()]))
    return out, explored, pruned


def _homogeneous(p: P.Poly) -> int | None:
    """The common total degree in p, q of a polynomial in p, q only (-1 for 0), else None."""
    degs = set()
    for mono in p:
        if any(a[0] != "v" or a[1] not in (PV, QV) for a, _ in mono):
            return None
        degs.add(sum(k for _, k in mono))
    return -1 if not degs else degs.pop() if len(degs) == 1 else None


def interface_cells(F: E, a: Fraction) -> tuple[list, dict]:
    """The sign cells of G = F - a*uL in the differences p, q: [{"atoms": [(c_p, c_q)], "N": {m: Poly},
    "D": Poly}] with G = sum_m lam^m N_m / D on the closed cone {c_p p + c_q q >= 0}. Raises OutOfScope."""
    extra = variables(F) - {"uLL", "uL", "uR", "lam"}
    if extra:
        raise OutOfScope(f"the flux uses {sorted(extra)}; this form needs F(uLL, uL, uR) on a three-point window")
    raw, explored, pruned = _cells(E("sub", (F, E("mul", (lit(a), var("uL"))))))
    sub = {"uLL": P.add(P.var("uL"), P.var(PV), -1), "uR": P.add(P.var("uL"), P.var(QV))}
    out = []
    for n, d, atoms in raw:
        lin = []
        for at in atoms:
            x = P.subst(at, sub)
            if not x:
                continue
            got = _lin2(x)
            if got is None:
                raise OutOfScope(f"the sign-cell atom {P.show(at)} >= 0 is not a linear form in uL - uLL, uR - uL")
            lin.append(got)
        dparts = _lam_parts(P.subst(d, sub))              # a power of lam in the denominator moves to N
        if len(dparts) != 1:
            raise OutOfScope("on a sign cell the denominator of F - a*uL is not lam^j times a form free of lam")
        (j, d), = dparts.items()
        k = _homogeneous(d)
        if k is None or k < 0:
            raise OutOfScope("on a sign cell the denominator of F - a*uL is not a homogeneous form in uL - uLL, "
                             "uR - uL")
        parts = {}
        for m, g in ((m - j, g) for m, g in _lam_parts(P.subst(n, sub)).items()):
            if not g:
                continue
            if _homogeneous(g) != k + 1:
                raise OutOfScope("on a sign cell F - a*uL is not translation invariant and positively homogeneous "
                                 "of degree 1 in uL - uLL, uR - uL")
            parts[m] = g
        out.append({"atoms": lin, "N": parts, "D": d})
    return out, {"retained": len(out), "explored": explored, "pruned (lower-dimensional, certified)": pruned}


def _ev2(p: P.Poly, pt: tuple) -> Fraction:
    return P.evaluate(p, {PV: Fraction(pt[0]), QV: Fraction(pt[1])})


def at_point(cells: list, pt: tuple) -> dict:
    """{m: value of the lam^m part of G} at the point (p, q), from a closed cell containing it whose
    denominator is non-zero there (any such cell gives the value of G there)."""
    for c in cells:
        if all(cp * pt[0] + cq * pt[1] >= 0 for cp, cq in c["atoms"]) and _ev2(c["D"], pt):
            den = _ev2(c["D"], pt)
            return {m: _ev2(g, pt) / den for m, g in c["N"].items()}
    raise P.Undecided(f"no sign cell gives G at (p, q) = {pt} (the cells do not cover the plane, or a denominator "
                      "vanishes there)")


def decompose(cells: list) -> tuple[dict, dict, list]:
    """(alpha, beta, L): G = sum_m lam^m (alpha_m q + beta_m L) with L = (numerator, D) per cell. Raises
    OutOfScope if the rest after alpha has rank > 1 over the powers of lam."""
    alpha = {m: v for m, v in at_point(cells, (Fraction(0), Fraction(1))).items() if v}
    rest = []
    for c in cells:
        ms = set(c["N"]) | set(alpha)
        r = {m: P.add(c["N"].get(m, {}), P.scale(P.mul(P.var(QV), c["D"]), alpha.get(m, 0)), -1) for m in ms}
        rest.append({m: x for m, x in r.items() if x})
    ms = sorted({m for r in rest for m in r})
    if not ms:
        return alpha, {}, [({}, c["D"]) for c in cells]
    m0 = ms[0]
    L = [(r.get(m0, {}), c["D"]) for r, c in zip(rest, cells)]
    beta = {m0: Fraction(1)}
    bad = OutOfScope("F - a*uL is not alpha(lam)*(uR - uL) + beta(lam)*L with one limited slope L")
    for m in ms[1:]:
        j = next(j for j, r in enumerate(rest) if m in r)
        if not L[j][0]:
            raise bad
        mono = next(iter(L[j][0]))
        b = rest[j][m].get(mono, Fraction(0)) / L[j][0][mono]
        for r, (n, _) in zip(rest, L):
            if P.add(r.get(m, {}), P.scale(n, b), -1):
                raise bad
        beta[m] = b
    return alpha, beta, L


def in_nu(coeffs: dict, a: Fraction) -> list:
    """lam * sum_m c_m lam^m with lam = nu/a, as a coefficient list in nu. Raises OutOfScope on a
    negative power of nu."""
    out: list = []
    for m, c in coeffs.items():
        if m + 1 < 0:
            raise OutOfScope(f"lam^{m + 1} in lam*G: not a polynomial in nu")
        out = U.add(out, [Fraction(0)] * (m + 1) + [c / a ** (m + 1)])
    return out


def _on_line(p: P.Poly, base: tuple, d: tuple) -> list:
    """p(base + t*d) as a coefficient list in t."""
    t = P.var("_t")
    x = P.subst(p, {PV: P.add(P.const(base[0]), P.scale(t, d[0])), QV: P.add(P.const(base[1]), P.scale(t, d[1]))})
    out = [Fraction(0)] * (1 + max((dict(m).get(("v", "_t"), 0) for m in x), default=0))
    for m, c in x.items():
        out[dict(m).get(("v", "_t"), 0)] += c
    return U.trim(out)


def _bound(c: list) -> Fraction:
    """A bound beyond every real root of c (Cauchy)."""
    c = U.trim(c)
    return 1 + max((abs(x / c[-1]) for x in c[:-1]), default=Fraction(0))


def _roots_in(c: list, lo, hi) -> int:
    """Distinct real roots of c in the open interval (lo, hi), None ends infinite."""
    c = U.trim(c)
    if U.deg(c) <= 0:
        return 0
    s = U.gcd(c, U.derivative(c))
    sq = U.divmod_(c, s)[0] if U.deg(s) > 0 else c
    m = _bound(sq)
    a, b = (-m if lo is None else lo), (m if hi is None else hi)
    return U.roots_open(U.sturm_sequence(sq), a, b) if a < b else 0


def _rational_roots(c: list) -> list:
    """The rational roots of c (rational root theorem on the integer-scaled polynomial)."""
    from math import gcd, isqrt, lcm
    c = U.trim(c)
    out = []
    while c and c[0] == 0:
        out.append(Fraction(0))
        c = c[1:]
    if U.deg(c) <= 0:
        return out
    den = lcm(*(x.denominator for x in c))
    ints = [int(x * den) for x in c]
    a0, an = abs(ints[0]), abs(ints[-1])
    if max(a0, an) > 10 ** 12:
        raise OutOfScope("coefficients too large for the rational-root search")
    divs = lambda n: {d for k in range(1, isqrt(n) + 1) if n % k == 0 for d in (k, n // k)}
    for p_ in divs(a0):
        for q_ in divs(an):
            for x in (Fraction(p_, q_), Fraction(-p_, q_)):
                if U.ev(c, x) == 0 and x not in out:
                    out.append(x)
    return out


def _extremes(n: list, d: list, lo, hi) -> tuple:
    """(inf, sup) of n/d over [lo, hi] (None ends infinite; an infinite inf or sup is None), exactly."""
    g = U.gcd(n, d) if U.trim(n) else [Fraction(1)]
    if U.deg(g) > 0:
        n, d = U.divmod_(n, g)[0], U.divmod_(d, g)[0]
    n, d = U.trim(n), U.trim(d)
    if _roots_in(d, lo, hi) or any(e is not None and U.ev(d, e) == 0 for e in (lo, hi)):
        return None, None                                         # a pole in the closed interval
    vals, inf_, sup_ = [], False, False
    for e in (lo, hi):
        if e is not None:
            vals.append(U.ev(n, e) / U.ev(d, e))
    for e, sgn in ((lo, -1), (hi, 1)):
        if e is None:                                              # the limit at -infinity / +infinity
            dn, dd = U.deg(n), U.deg(d)
            if dn < dd:
                vals.append(Fraction(0))
            elif dn == dd:
                vals.append(n[-1] / d[-1])
            else:
                lead = n[-1] / d[-1] * (sgn ** (dn - dd))
                inf_, sup_ = inf_ or lead < 0, sup_ or lead > 0
    crit = U.add(U.mul(U.derivative(n), d), U.mul(n, U.derivative(d)), -1)
    if U.trim(crit):
        inside = [x for x in _rational_roots(crit) if (lo is None or x > lo) and (hi is None or x < hi)]
        rest = crit
        for x in _rational_roots(crit):
            while U.deg(rest) > 0 and U.ev(rest, x) == 0:
                rest = U.divmod_(rest, [-x, Fraction(1)])[0]
        if _roots_in(rest, lo, hi):
            raise OutOfScope("an extremum of the limiter on a branch lies at an irrational point")
        vals += [U.ev(n, x) / U.ev(d, x) for x in inside]
    return (None if inf_ else min(vals)), (None if sup_ else max(vals))


def ranges(cells: list, L: list) -> dict:
    """{family: (inf, sup)} of phi = L/q and xi = L/p (None for an infinite end), exactly: on the line of
    each family the cells cut intervals on which L is a rational function of one variable."""
    out = {}
    for fam, (base, d, s) in FAMILIES.items():
        pieces = []
        for c, (ln, ld) in zip(cells, L):
            lo, hi, empty = None, None, False
            for cp, cq in c["atoms"]:
                k, k0 = cp * d[0] + cq * d[1], cp * base[0] + cq * base[1]       # the atom is k t + k0 >= 0
                if k == 0:
                    empty |= k0 < 0
                elif k > 0:
                    lo = -k0 / k if lo is None else max(lo, -k0 / k)
                else:
                    hi = -k0 / k if hi is None else min(hi, -k0 / k)
            if empty or (lo is not None and hi is not None and lo > hi):
                continue
            pieces.append((lo, hi, [s * x for x in _on_line(ln, base, d)], _on_line(ld, base, d)))
        _covers_line(pieces, fam)
        ext = [_extremes(n, dd, lo, hi) if U.trim(n) else (Fraction(0), Fraction(0)) for lo, hi, n, dd in pieces]
        out[fam] = (None if any(e[0] is None for e in ext) else min(e[0] for e in ext),
                    None if any(e[1] is None for e in ext) else max(e[1] for e in ext))
    return out


def _covers_line(pieces: list, fam: str) -> None:
    """The intervals of the pieces cover the whole line (they must, as the cells cover the plane)."""
    reach = None                                      # covered so far: (-inf, reach]
    todo = sorted(pieces, key=lambda x: (x[0] is not None, x[0] or 0))
    if not todo or todo[0][0] is not None:
        raise P.Undecided(f"the cells do not cover the line of {fam} at -infinity (a bug)")
    for lo, hi, *_ in todo:
        if lo is not None and reach is not None and lo > reach:
            raise P.Undecided(f"the cells leave a gap on the line of {fam} after {reach} (a bug)")
        if hi is None:
            return
        reach = hi if reach is None else max(reach, hi)
    raise P.Undecided(f"the cells do not cover the line of {fam} at +infinity (a bug)")


# ---------------------------------------------------------------- the conditions

def _show(c: list) -> str:
    return U.show(c, "nu")


def decide(c0: list, terms: list, lo: Fraction, hi: Fraction) -> tuple[dict | None, str]:
    """c0(nu) + sum_k c_k(nu) v_k >= 0 for every nu in [lo, hi] and independent v_k in their ranges
    (inf, sup), None ends infinite. Returns (certificate, "") or (None, why not)."""
    choices, signs = [], {}
    for ck, (vl, vh) in terms:
        ck = U.trim(ck)
        if not ck:
            continue
        if vl is None and vh is None:
            return None, f"a range is unbounded both ways while its coefficient {_show(ck)} is not 0"
        if vh is None or vl is None:
            need = ck if vh is None else U.add([], ck, -1)
            got = U.nonneg_on(need, lo, hi)
            if not got["nonneg"]:
                return None, (f"the coefficient {_show(ck)} of an unbounded range has the wrong sign at nu = "
                              f"{got['counterexample']['x']}")
            signs[_show(ck)] = ">= 0" if vh is None else "<= 0"
        choices.append([(ck, v) for v in dict.fromkeys(x for x in (vl, vh) if x is not None)])
    corners = []
    for combo in product(*choices):
        p = U.trim(c0)
        for ck, v in combo:
            p = U.add(p, [x * v for x in ck])
        got = U.nonneg_on(p, lo, hi)
        corners.append({"at": [str(v) for _, v in combo], "polynomial": _show(p),
                        "certificate": U.jsonable(got["certificate"])})
        if not got["nonneg"]:
            return None, f"{_show(p)} < 0 at nu = {got['counterexample']['x']} (values {[str(v) for _, v in combo]})"
    return {"coefficient signs": signs, "corners": corners}, ""


def _zero(cells: list, pts) -> bool:
    return all(not any(at_point(cells, pt).values()) for pt in pts)


ONE, ZERO = Fraction(1), Fraction(0)
OWN_ZERO = ((ONE, ZERO), (-ONE, ZERO))          # q = 0: G(p, 0) = 0
UP_ZERO = ((ZERO, ONE), (ZERO, -ONE))           # p = 0: G(0, q) = 0


def conditions(form: str, A: list, B: list, rg: dict) -> dict:
    """{name: (c0, [(c_k, range)])} for the split `form`; each must be >= 0 on the nu-range."""
    nu, one = [ZERO, ONE], [ONE]
    neg = lambda c: U.add([], c, -1)
    if form == "upwind":
        out = {}
        for s in "+-":
            box = [(B, rg[f"xi{s}"]), (neg(B), rg[f"phi{s}"])]
            out[f"D >= 0 (Delta_(i-1/2) {s})"] = (nu, box)
            out[f"D <= 1 (Delta_(i-1/2) {s})"] = (U.add(one, nu, -1), [(neg(c), r) for c, r in box])
        return out
    out = {}
    for s in "+-":
        phi = rg[f"phi{s}"]
        out[f"C >= 0 (Delta_(i+1/2) {s})"] = (neg(A), [(neg(B), phi)])
        out[f"D >= 0 (Delta_(i-1/2) {s})"] = (U.add(nu, A, -1), [(neg(B), phi)])
        out[f"C_j + D_j <= 1 (Delta_(j+1/2) {s})"] = (U.add(U.add(one, nu, -1), A, 2), [(U.add([], B, 2), phi)])
    for s, t in product("+-", repeat=2):
        out[f"C_i + D_(i-1) <= 1 (Delta_(i+1/2) {s}, Delta_(i-1/2) {t})"] = (
            U.add(U.add(one, nu, -1), A, 2), [(B, rg[f"phi{s}"]), (B, rg[f"phi{t}"])])
    return out


def certify(spec: dict, lo: Fraction, hi: Fraction) -> dict:
    """Harten's form with general C, D on the nu-range [lo, hi]. Returns {"verified": bool, "reason",
    and the certificate}. Raises OutOfScope (or Undecided, NonlinearFlux) outside the class."""
    from . import limiters
    a = limiters._advection(spec)
    if a <= 0:
        raise OutOfScope("a < 0: the mirror image of this form is not implemented")
    F = checks.numerical_flux(spec)
    if F is None:
        raise OutOfScope("no numerical flux declared")
    cells, cs = interface_cells(F, a)
    alpha, beta, L = decompose(cells)
    A, B = in_nu(alpha, a), in_nu(beta, a)
    rg = ranges(cells, L)
    own_zero, up_zero = _zero(cells, OWN_ZERO), _zero(cells, UP_ZERO)
    wit = {"a": str(a), "interface cells": cs,
           "flux": "F = a*uL + alpha(lam)*(uR - uL) + beta(lam)*L(uLL, uL, uR), L free of lam",
           "alpha": {str(m): str(v) for m, v in sorted(alpha.items())},
           "beta": {str(m): str(v) for m, v in sorted(beta.items())},
           "A(nu) = lam*alpha": _show(A), "B(nu) = lam*beta": _show(B),
           "ranges": {f: [None if x is None else str(x) for x in r] for f, r in rg.items()},
           "G(p, 0) = 0": own_zero, "G(0, q) = 0": up_zero, "tried": {}}
    for form in ("upwind", "flux"):
        if form == "upwind" and U.trim(A):
            wit["tried"][form] = f"needs alpha = 0, here A(nu) = {_show(A)}"
            continue
        if not own_zero or (form == "upwind" and not up_zero):
            wit["tried"][form] = "the difference-zero identities fail"
            continue
        certs, why = {}, ""
        for name, (c0, terms) in conditions(form, A, B, rg).items():
            cert, why = decide(c0, terms, lo, hi)
            if cert is None:
                why = f"{name}: {why}"
                break
            certs[name] = cert
        if why:
            wit["tried"][form] = why
            continue
        wit.update(form=form, conditions=certs, lam1=str(_lam1(beta)))
        return {"verified": True, "reason": "", **wit}
    return {"verified": False, "reason": "; ".join(f"{k} split: {v}" for k, v in wit["tried"].items()), **wit}


def _lam1(beta: dict) -> Fraction:
    """A rational lam at which beta(lam) != 0 (where L = (G - alpha q)/beta can be read off), 1 if beta = 0."""
    for x in (Fraction(1), Fraction(1, 2), Fraction(1, 3), Fraction(2), Fraction(3)):
        if not beta or sum(c * x ** m for m, c in beta.items()):
            return x
    raise AssertionError("beta has more roots than its degree")
