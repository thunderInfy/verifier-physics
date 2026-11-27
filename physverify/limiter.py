"""The scaling (bound-preserving) limiter of Zhang and Shu, decided exactly for degrees k <= 3 (claim kinds
`limiter_keeps_average`, `limiter_bounds`, `limiter_accuracy`).

Usage: python -m physverify.limiter [paths]   (by default benchmark/reconstruction/limiter)

A spec (benchmark/reconstruction/limiter/*.json) gives the degree k of p, in the local coordinate y in I = [-1/2, 1/2] of a cell;
the centre c of the scaling (`center`: "avg", the cell average ubar, or a point y0); the set S where
M_x = max_S p and m_x = min_S p are taken (`extrema_over`: "cell" or a list of points of I); and the terms of
theta (`theta`, a subset of "1", "upper", "lower"):

    upper = |M - c| / |M_x - c|,  lower = |m - c| / |m_x - c|,  theta = min of the terms,  p~ = c + theta (p - c).

A ratio term with a zero denominator is left out (p is then constant on S at the value c), and theta = 1 if no
term is left. Each claim is for every p of degree <= k and all m <= M, with c in [m, M] unless the claim says
`"average_in_bounds": false`.

  limiter_keeps_average  avg(p~) = avg(p). avg(p~) - avg(p) = (1 - theta)(c - avg p): VERIFIED iff c is the average
                         functional (an identity in the coefficients of p), otherwise a witness is searched for.
  limiter_bounds (on)    m <= p~(y) <= M for y in `on`. VERIFIED (c = avg) when theta has both ratio terms, the
                         hypothesis is assumed, and `on` is dominated by S at degree k (max_on p <= max_S p for every
                         p of degree k): then for y in `on`, p(y) - c <= M_x - c, and theta (M_x - c) <= |M - c| =
                         M - c if M_x > c, while theta (p(y) - c) <= 0 <= M - c otherwise; the same below.
                         Domination, exactly: k = 0 always; S = I always; k = 1 iff every point of `on` is in
                         [min S, max S] (`on` = I: both cell ends in S); k >= 2 iff `on` is a subset of S (else
                         -(y - y')^2 peaks at a point y' of `on` outside S).
  limiter_accuracy       there is C with max_I |p~ - p| <= C d, d = max_I dist(p(y), [m, M]) (d <= max_I |p - u| for
                         every u with values in [m, M], so an accurate p stays accurate). VERIFIED (c = avg) when
                         the term 1 is in theta and avg = sum_s w_s p(s) with w_s >= 0 over S for degree k (S = I:
                         nothing to check), with C = K_k, a certified upper bound of
                         sup { max_I |q| / max_I q : avg q = 0, deg q <= k, q != 0 }.
                         Proof: p~ - p = (theta - 1)(p - c), 0 <= theta <= 1. If theta = upper < 1, either M >= c,
                         so M_x(S) - c >= 0 by the weights and > M - c, and 1 - theta = (M_x(S) - M)/(M_x(S) - c)
                         <= (M_x(I) - M)/(M_x(I) - c), giving (1 - theta) max|p - c| <= K_k (M_x(I) - M) <= K_k d;
                         or M < c, and (1 - theta) max|p - c| <= K_k (M_x(I) - c) <= K_k (M_x(I) - M) = K_k d.
                         The lower term is the same for -p. The hypothesis c in [m, M] is not used.
                         K_k: with the k + 1 equally spaced nodes x_a of I, Lagrange basis L_a and Newton-Cotes
                         weights w_a = avg L_a (checked > 0), a zero-mean q with max_I q = 1 has values v_a <= 1 at
                         the nodes with sum w_a v_a = 0; the minimum of q(y) = sum L_a(y) v_a over that polytope is
                         at a vertex (all v = 1 but one), so min_I q >= 1 - max_{a, y} L_a(y)/w_a and
                         K_k <= max(1, max_a B_a / w_a - 1) with B_a >= max_I L_a certified by Sturm
                         (univariate.nonneg_on): 1, 5, 7 for k = 1, 2, 3. Sharper, by duality: K_k <= 1/w - 1 if
                         avg P >= w P(y0) for all y0 in I and P >= 0 on I of degree k (take P = (M - q)/(M + 1)
                         with q(y0) = min q = -1, M = max q), and that holds when Hankel matrices of
                         avg - w delta_y0 are PSD for all y0 (Markov-Lukacs; `_moment_certificate`, Sturm in y0).
                         With w = 1/(K + 1) for the witness ratios K of LOWER_WITNESS, this certifies K_k = 1, 3, 5
                         exactly (the witnesses attain them).
When the argument does not apply, a REFUTED verdict needs an explicit datum (p, m, M), from a fixed list of simple
candidates, that breaks the claim by exact evaluation: for accuracy, a p with d = 0 (m <= p <= M on I, certified by
Sturm) and theta != 1, so p~ != p. If no candidate works the verdict is UNKNOWN. Extrema of p over I are computed
exactly from the roots of p' (degree <= 2, so rational or a surd); a candidate with an irrational extremum in I is
skipped. Fraction arithmetic only; nothing is sampled.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

from . import cellaverage as CA, claimkinds
from .schemes import univariate as U

VERIFIED, REFUTED, UNKNOWN = "VERIFIED", "REFUTED", "UNKNOWN"
CLAIMS = ("limiter_keeps_average", "limiter_bounds", "limiter_accuracy")
claimkinds.require("reconstruction", CLAIMS)
BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "limiter"
K_MAX = 3
TERMS = ("1", "upper", "lower")
LO, HI = Fraction(-1, 2), Fraction(1, 2)


class Unknown(Exception):
    pass


# ---------------------------------------------------------------- polynomials on the cell

def avg_vec(k: int) -> list[Fraction]:
    return CA.functional([0, "avg"], k, [0])


def average(p: list) -> Fraction:
    return CA._dot(avg_vec(len(p) - 1), p) if p else Fraction(0)


def _isqrt_frac(x: Fraction):
    """sqrt(x) if it is rational, else None (x >= 0)."""
    from math import isqrt
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    return Fraction(a, b) if a * a == x.numerator and b * b == x.denominator else None


def critical_points(p: list) -> list[Fraction]:
    """The roots of p' in the open cell, all rational; Unknown if p' has an irrational root there."""
    d = U.trim(U.derivative(U.trim(p)))
    if U.deg(d) <= 0:
        return []
    if U.deg(d) == 1:
        r = -d[0] / d[1]
        return [r] if LO < r < HI else []
    if U.deg(d) == 2:
        c0, c1, c2 = d
        disc = c1 * c1 - 4 * c2 * c0
        if disc < 0:
            return []
        s = _isqrt_frac(disc)
        if s is None:
            if U.roots_open(U.sturm_sequence(U.monic(d)), LO, HI):
                raise Unknown("an extremum of p in the cell is irrational")
            return []
        return sorted({r for r in ((-c1 + s) / (2 * c2), (-c1 - s) / (2 * c2)) if LO < r < HI})
    raise Unknown("degree above 3")


def points_of(S, p: list) -> list[Fraction]:
    """Points where max_S p and min_S p are attained (for S = the cell: the ends and the critical points)."""
    return [LO, HI] + critical_points(p) if S == "cell" else list(S)


def extrema(p: list, S) -> tuple[Fraction, Fraction]:
    vals = [U.ev(p, y) for y in points_of(S, p)]
    return max(vals), min(vals)


def centre_value(p: list, center) -> Fraction:
    return average(p) if center == "avg" else U.ev(p, center)


def theta(L: dict, p: list, m: Fraction, M: Fraction) -> Fraction:
    c = centre_value(p, L["center"])
    Mx, mx = extrema(p, L["S"])
    terms = []
    for t in L["terms"]:
        if t == "1":
            terms.append(Fraction(1))
        elif t == "upper" and Mx != c:
            terms.append(abs(M - c) / abs(Mx - c))
        elif t == "lower" and mx != c:
            terms.append(abs(m - c) / abs(mx - c))
    return min(terms) if terms else Fraction(1)


def limited(L: dict, p: list, m: Fraction, M: Fraction) -> tuple[list, Fraction]:
    th, c = theta(L, p, m, M), centre_value(p, L["center"])
    q = U.add([th * a for a in p], [c - th * c])
    return q, th


def _show(p: list) -> str:
    return " + ".join(f"{a}*y^{n}" for n, a in enumerate(p)) or "0"


def _pad(p: list, k: int) -> list:
    p = U.trim(p)
    return p + [Fraction(0)] * (k + 1 - len(p))


# ---------------------------------------------------------------- the spec

def parse_spec(rec: dict) -> dict:
    k = rec["degree"]
    if not isinstance(k, int) or k < 0:
        raise ValueError("degree must be a non-negative integer")
    terms = list(rec["theta"])
    if not terms or any(t not in TERMS for t in terms):
        raise ValueError(f"theta is a non-empty list of terms from {TERMS}")
    S = rec["extrema_over"]
    S = "cell" if S == "cell" else [Fraction(str(y)) for y in S]
    if S != "cell" and (not S or any(abs(y) > HI for y in S)):
        raise ValueError("extrema_over is 'cell' or a non-empty list of points y in [-1/2, 1/2]")
    center = rec.get("center", "avg")
    center = "avg" if center == "avg" else Fraction(str(center))
    if center != "avg" and abs(center) > HI:
        raise ValueError("the centre is 'avg' or a point of the cell")
    return {"k": k, "terms": terms, "S": S, "center": center}


def _on(claim: dict):
    on = claim["on"]
    if on == "cell":
        return "cell"
    on = [Fraction(str(y)) for y in on]
    if not on or any(abs(y) > HI for y in on):
        raise ValueError("on is 'cell' or a non-empty list of points y in [-1/2, 1/2]")
    return on


# ---------------------------------------------------------------- candidate data (for REFUTED only)

def _candidates(k: int) -> list[list[Fraction]]:
    F = Fraction
    out = []
    if k >= 1:
        out += [[F(0), F(1)], [F(0), F(-1)], [F(1), F(1, 4)], [F(-1), F(1, 4)]]
    for j in range(2, k + 1):
        mono = [F(0)] * j + [F(1)]
        out += [mono, [-a for a in mono]]
    if k >= 2:
        for y0 in (F(0), F(1, 4), F(-1, 4), F(1, 3), F(-1, 3), F(1, 8), F(-1, 8)):
            out.append([-y0 * y0, 2 * y0, F(-1)])  # -(y - y0)^2
    if k == 0:
        out += [[F(1)], [F(-1)]]
    return [_pad(p, k) for p in out]


def _bound_values(p: list, S, extra) -> list[Fraction]:
    F = Fraction
    Mx, mx = extrema(p, S)
    vals = {F(0), F(1), F(-1), F(1, 4), F(-1, 4), F(1, 2), F(-1, 2), F(2), F(-2), Mx, mx, average(p)}
    for v in extra:
        vals |= {v, v / 2, 2 * v}
    return sorted(vals)


def _hyp_ok(L: dict, p: list, m: Fraction, M: Fraction, assume: bool) -> bool:
    return m <= M and (not assume or m <= centre_value(p, L["center"]) <= M)


def _witness(p, m, M, th, **kw) -> dict:
    return {"p": _show(p), "m": str(m), "M": str(M), "theta": str(th), **{k: str(v) for k, v in kw.items()}}


def _search(L: dict, assume: bool, test, polys=None, extra_points=()):
    """The first (p, m, M) of the candidates for which test(p, m, M, p~, theta) returns a witness dict."""
    for p in polys if polys is not None else _candidates(L["k"]):
        try:
            pts = sorted(set(points_of(L["S"], p)) | set(points_of("cell", p)) | set(extra_points))
            vals = _bound_values(p, L["S"], [U.ev(p, y) for y in pts])
            for m, M in product(vals, vals):
                if not _hyp_ok(L, p, m, M, assume):
                    continue
                pt, th = limited(L, p, m, M)
                w = test(p, m, M, pt, th)
                if w:
                    return w
        except Unknown:
            continue
    return None


# ---------------------------------------------------------------- the decisions

def keeps_average(L: dict, assume: bool) -> dict:
    k = L["k"]
    a = avg_vec(k)
    cvec = a if L["center"] == "avg" else [L["center"] ** n for n in range(k + 1)]
    if a == cvec:
        return {"verdict": VERIFIED, "reason": "the centre is the average functional, so avg(p~) = c + theta (avg p - c) "
                "= avg p identically in the coefficients of p"}

    def test(p, m, M, pt, th):
        if average(pt) != average(p):
            return _witness(p, m, M, th, average_p=average(p), average_limited=average(pt))
    w = _search(L, assume, test)
    if w:
        return {"verdict": REFUTED, "witness": w, "reason": "the centre is not the average: with this datum "
                "avg(p~) != avg(p) (exact evaluation)"}
    return {"verdict": UNKNOWN, "reason": "the centre is not the average and no candidate datum breaks the claim"}


def dominated(on, S, k: int) -> bool:
    if k == 0 or S == "cell":
        return True
    if k == 1:
        pts = [LO, HI] if on == "cell" else on
        return all(min(S) <= y <= max(S) for y in pts)
    return on != "cell" and set(on) <= set(S)


def bounds(L: dict, on, assume: bool) -> dict:
    if L["center"] != "avg":
        return {"verdict": UNKNOWN, "reason": "only the limiter centred at the average is decided for the bounds"}
    k = L["k"]
    ok = {"upper and lower terms in theta": {"upper", "lower"} <= set(L["terms"]),
          "average in [m, M] assumed": assume,
          f"`on` dominated by the extrema set at degree {k}": dominated(on, L["S"], k)}
    if all(ok.values()):
        return {"verdict": VERIFIED, "conditions": ok, "reason": "theta >= 0 is at most |M - ubar|/|M_x - ubar| and "
                "|m - ubar|/|m_x - ubar|, ubar is in [m, M], and every point of `on` has p between m_x and M_x, so "
                "p~ = ubar + theta (p - ubar) is in [m, M] there (module docstring)"}
    extra = [] if on == "cell" else on

    def test(p, m, M, pt, th):
        for y in sorted(set(points_of("cell", p) if on == "cell" else on) | (set(
                points_of("cell", pt)) if on == "cell" else set())):
            v = U.ev(pt, y)
            if not m <= v <= M:
                return _witness(p, m, M, th, y=y, limited_value=v)
    w = _search(L, assume, test, extra_points=extra)
    if w:
        return {"verdict": REFUTED, "conditions": ok, "witness": w, "reason": "this datum (exact evaluation) has "
                "p~(y) outside [m, M] at a point y of `on`"}
    return {"verdict": UNKNOWN, "conditions": ok, "reason": "the argument needs every condition, and no candidate "
            "datum breaks the claim"}


def _upper_bound(p: list) -> Fraction:
    """A rational B >= max_I p, certified by Sturm (B - p >= 0 on I); the guess comes from a grid."""
    g = max(U.ev(p, LO + Fraction(j, 64)) for j in range(65))
    for eps in (Fraction(0), Fraction(1, 1000), Fraction(1, 100), Fraction(1, 10), Fraction(1), Fraction(10)):
        B = g + eps * (1 + abs(g))
        if U.nonneg_on(U.add([B], p, -1), LO, HI)["nonneg"]:
            return B
    raise Unknown("no certified upper bound found")


# zero-mean q of degree k with max_I |q| / max_I q as large as we found (numerically, then exactly): 1, 3, 5
LOWER_WITNESS = {1: [Fraction(0), Fraction(1)],                                       # y
                 2: [Fraction(1, 12), Fraction(1, 3), Fraction(-1)],                  # 1/9 - (y - 1/6)^2
                 3: [Fraction(1, 24), Fraction(0), Fraction(-1, 2), Fraction(-1)]}    # 1/24 - y^2/2 - y^3


def abs_max_ratio(q: list) -> Fraction:
    """max_I |q| / max_I q for a zero-mean q != 0, exactly (extrema at the ends and the roots of q')."""
    Mx, mx = extrema(q, "cell")
    return max(Mx, -mx) / Mx


def _moment_certificate(k: int, w: Fraction) -> list | None:
    """Sturm certificates that avg P >= w P(y0) for every y0 in I and every P >= 0 on I of degree <= k, or None.
    By the Markov-Lukacs theorem such P is A^2 + (1/4 - y^2) B^2 (k = 2n) or (y + 1/2) A^2 + (1/2 - y) B^2
    (k = 2n + 1), deg A <= n, deg B <= n - 1 resp. n; so it suffices that, for each multiplier g, the Hankel
    matrix H_ij(y0) = Lam(g y^(i+j)), Lam(f) = avg f - w f(y0), is positive semidefinite for all y0 in I. Each H
    is 1 x 1 or 2 x 2 for k <= 3: its diagonal entries and determinant, polynomials in y0, are certified >= 0 on
    I. Then for a zero-mean q with q(y0) = min_I q = -1 and max_I q = M, P = (M - q)/(M + 1) gives
    M / (M + 1) >= w, i.e. max_I |q| / max_I q <= 1/w - 1."""
    n = k // 2
    if k % 2 == 0:
        mults = [([Fraction(1)], n), ([Fraction(1, 4), Fraction(0), Fraction(-1)], n - 1)]
    else:
        mults = [([HI, Fraction(1)], n), ([HI, Fraction(-1)], n)]
    lam = lambda f: U.add([average(f)], [w * a for a in f], -1)    # Lam(f) as a polynomial in y0
    certs = []
    for g, deg in mults:
        if deg < 0:
            continue
        if deg > 1:
            return None
        H = [[lam(U.mul(g, [Fraction(0)] * (i + j) + [Fraction(1)])) for j in range(deg + 1)] for i in range(deg + 1)]
        polys = [H[i][i] for i in range(deg + 1)]
        if deg == 1:
            polys.append(U.add(U.mul(H[0][0], H[1][1]), U.mul(H[0][1], H[1][0]), -1))
        for p in polys:
            c = U.nonneg_on(p, LO, HI)
            if not c["nonneg"]:
                return None
            certs.append({"multiplier": U.show(g, "y"), "polynomial in y0": U.show(p, "y0")})
    return certs


def accuracy_constant(k: int) -> dict:
    """A certified upper bound K of K_k (module docstring) and the lower bound of an explicit witness. The upper
    bound is 1/w - 1 from the moment certificate with w = 1/(lower + 1) when it holds (then K is the supremum),
    else the Newton-Cotes bound."""
    if k == 0:
        return {"K": Fraction(1), "lower": Fraction(1), "method": "constant", "nodes": [], "weights": [], "bounds": []}
    out = _newton_cotes(k)
    q = LOWER_WITNESS.get(k)
    if q is not None:
        assert average(q) == 0
        lower = abs_max_ratio(q)
        out.update(lower=lower, witness=U.show(q, "y"))
        certs = _moment_certificate(k, 1 / (lower + 1))
        if certs is not None and lower < out["K"]:
            out.update(K=lower, method="moment certificate (Markov-Lukacs, Sturm)", certificate=certs)
    return out


def _newton_cotes(k: int) -> dict:
    """K_k <= max(1, max_a B_a / w_a - 1) from the Newton-Cotes nodes (module docstring)."""
    nodes = [LO + Fraction(a, k) for a in range(k + 1)]
    weights, Bs, ratio = [], [], Fraction(0)
    for a, xa in enumerate(nodes):
        La = [Fraction(1)]
        for b, xb in enumerate(nodes):
            if b != a:
                La = U.mul(La, [-xb / (xa - xb), 1 / (xa - xb)])
        w = average(La)
        if w <= 0:
            raise Unknown(f"a Newton-Cotes weight is not positive at degree {k}")
        B = _upper_bound(La)
        weights.append(w)
        Bs.append(B)
        ratio = max(ratio, B / w)
    return {"K": max(Fraction(1), ratio - 1), "method": "Newton-Cotes", "newton_cotes_K": max(Fraction(1), ratio - 1),
            "nodes": nodes, "weights": weights, "bounds": Bs}


def positive_weights(L: dict):
    """(True, w) if avg = sum_s w_s p(s) for degree k with w >= 0 (S = the cell: nothing to check), else (False, why)."""
    if L["S"] == "cell":
        return True, None
    k = L["k"]
    rows = [[y ** n for n in range(k + 1)] for y in L["S"]]
    try:
        w, res = CA.solve(rows, avg_vec(k))
    except CA.Unknown:
        raise Unknown("the point evaluations on S are linearly dependent at this degree; the weights need a linear "
                      "programme, not done")
    if any(res):
        return False, "not in the span of the point values"
    w = [x[0] if x else Fraction(0) for x in w]
    return (True, w) if all(x >= 0 for x in w) else (False, w)


def _farkas_polys(L: dict, why) -> list[list]:
    """Zero-mean q with q < 0 at every point of S, when the average is not a non-negative combination."""
    k, S = L["k"], L["S"]
    rows = [[y ** n for n in range(k + 1)] for y in S]
    a = avg_vec(k)
    if isinstance(why, list):  # unique weights, some negative
        pos = sum(x for x in why if x >= 0)
        neg = -sum(x for x in why if x < 0)
        q = CA._point_solution(rows, [Fraction(-1) if x >= 0 else -pos / neg for x in why])
        return [q]
    out = []
    for j in range(k + 1):  # a kernel vector v of the evaluations with avg v = 1; q = v - 1
        e = [Fraction(int(i == j)) for i in range(k + 1)]
        corr = CA._point_solution(rows, [CA._dot(r, e) for r in rows])
        v = [x - y for x, y in zip(e, corr)]
        if any(CA._dot(r, v) for r in rows) or not CA._dot(a, v):
            continue
        s = 1 / CA._dot(a, v)
        out.append(U.add([s * x for x in v], [Fraction(1)], -1))
        break
    return [_pad(q, k) for q in out]


def accuracy(L: dict, assume: bool) -> dict:
    if L["center"] != "avg":
        return {"verdict": UNKNOWN, "reason": "only the limiter centred at the average is decided for the accuracy"}
    pos, w = positive_weights(L)
    ok = {"term 1 in theta": "1" in L["terms"], "average a non-negative combination of the values on S": pos}
    if all(ok.values()):
        K = accuracy_constant(L["k"])
        out = {"verdict": VERIFIED, "conditions": ok, "C": str(K["K"]), "C_method": K["method"],
               "C_lower": str(K["lower"]), "C_lower_witness": K.get("witness", "1"),
               "newton_cotes": {"nodes": [str(x) for x in K["nodes"]], "weights": [str(x) for x in K["weights"]],
                                "max_L_bounds": [str(x) for x in K["bounds"]]},
               "reason": f"max_I |p~ - p| <= {K['K']} * max_I dist(p, [m, M]) for every p of degree <= {L['k']} and "
                         "all m <= M (module docstring; the constant is certified by Sturm); the hypothesis ubar in "
                         "[m, M] is not used"}
        if w:
            out["weights_on_S"] = [str(x) for x in w]
        return out

    def test(p, m, M, pt, th):
        if th == 1 or not U.trim(U.add(p, [average(p)], -1)):
            return None
        if not (U.nonneg_on(U.add([M], p, -1), LO, HI)["nonneg"] and U.nonneg_on(U.add(p, [m], -1), LO, HI)["nonneg"]):
            return None  # d = 0 needs m <= p <= M on the cell, certified
        return _witness(p, m, M, th, overshoot=0, sup_difference_at_least=abs(th - 1) * max(
            abs(U.ev(p, y) - average(p)) for y in points_of("cell", p)))

    polys = _candidates(L["k"])
    if not pos:
        qs = _farkas_polys(L, w)
        polys = qs + [[-x for x in q] for q in qs] + polys
    w_ = _search(L, assume, test, polys=polys)
    if w_:
        return {"verdict": REFUTED, "conditions": ok, "witness": w_, "reason": "this datum lies in [m, M] on the "
                "whole cell (overshoot 0, certified by Sturm) but theta != 1, so p~ != p and no constant C works"}
    return {"verdict": UNKNOWN, "conditions": ok, "reason": "the argument needs every condition, and no candidate "
            "datum breaks the claim"}


DECIDE = {"limiter_keeps_average": lambda L, c, a: keeps_average(L, a),
          "limiter_bounds": lambda L, c, a: bounds(L, _on(c), a),
          "limiter_accuracy": lambda L, c, a: accuracy(L, a)}


def check_claim(rec: dict, claim: dict) -> dict:
    try:
        L = parse_spec(rec)
        assume = claim.get("average_in_bounds", True)
        if not isinstance(assume, bool):
            raise ValueError("average_in_bounds is true or false")
        if claim["claim"] not in DECIDE:
            raise ValueError(f"unknown claim {claim['claim']}")
        if L["k"] > K_MAX:
            return {"verdict": UNKNOWN, "reason": f"degrees above {K_MAX} are not decided"}
        return U.jsonable(DECIDE[claim["claim"]](L, claim, assume))
    except (KeyError, ValueError, TypeError) as e:
        return {"verdict": UNKNOWN, "reason": f"bad spec: {e}"}
    except Unknown as e:
        return {"verdict": UNKNOWN, "reason": str(e)}


def check(spec: dict) -> dict:
    return {"claims": [{"claim": c["claim"], **check_claim(spec["reconstruction"], c)} for c in spec["claims"]]}


def main(argv=None) -> int:
    paths = []
    for a in (argv if argv is not None else sys.argv[1:]) or [str(BENCH)]:
        p = Path(a)
        paths += sorted(p.glob("*.json")) if p.is_dir() else [p]
    print("| spec | claim | expected | verdict | detail |\n|---|---|---|---|---|")
    wrong = unsure = 0
    for path in paths:
        spec = json.loads(path.read_text())
        for c, r in zip(spec["claims"], check(spec)["claims"]):
            ok = r["verdict"] == c.get("expect")
            flag = "" if ok else ("  (UNSURE, differs)" if c.get("confidence") == "unsure" else "  (WRONG)")
            wrong += not ok and c.get("confidence") != "unsure"
            unsure += not ok and c.get("confidence") == "unsure"
            args = ", ".join(f"{k}={v}" for k, v in c.items() if k in ("on", "average_in_bounds"))
            detail = f"C = {r['C']}" if "C" in r else (json.dumps(r["witness"]) if "witness" in r else r.get("reason", ""))
            print(f"| {path.stem} | {c['claim']}({args}) | {c.get('expect')} | {r['verdict']}{flag} | {detail} |")
    print(f"\n{wrong} not as expected, {unsure} unsure expectations differ")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
