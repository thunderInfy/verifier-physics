"""Order of WENO-type reconstructions, decided exactly from the Taylor jet (claim kind
`reconstruction_order_p`).

Usage: python -m physverify.reconstruction [paths]   (by default benchmark/reconstruction)

A spec (benchmark/reconstruction/*.json) writes the reconstruction over stencil values v_k, named
`v0`, `vm1`, `vp1`, `vm2`, ... (v_{-1} is `vm1`): candidate values q_k at x_i + s dx (`point`, s),
linear weights d_k and, for `"kind": "js"`, smoothness indicators beta_k, with
alpha_k = d_k / (eps + beta_k)^q and omega_k = alpha_k / sum_j alpha_j; for `"kind": "linear"`,
omega_k = d_k / sum_j d_j; for `"kind": "z"` (WENO-Z, Borges et al.), with `"tau": [i, j]`,
alpha_k = d_k (1 + (tau / (eps + beta_k))^q), tau = |beta_i - beta_j|; for `"kind": "m"` (WENO-M, Henrick
et al.), the js weights mapped by g_k(w) = w (d_k + d_k^2 - 3 d_k w + w^2) / (d_k^2 + w (1 - 2 d_k)) and
renormalised. The data are point values f(x_i + k dx) (`point_values`) or cell
averages of u over [x_i + (k - 1/2) dx, x_i + (k + 1/2) dx] (`cell_averages`). The target is f
(or u) at x_i + s dx (`value`), or, for point values, `primitive`: the h of the finite-difference
flux form, whose sliding cell average is f, so that (h(x + dx/2) - h(x - dx/2)) / dx = f'(x).

A claim fixes the order p, the form, the regime and the eps scaling:
  form "point":            E = R(x_i + s dx) - T(x_i + s dx)
  form "flux_difference":  E = ((R - T) at x_i + s dx  -  (R - T) at x_i + (s - 1) dx) / dx, the
                           second reconstruction from the stencil shifted one cell left (the
                           conservative difference of the scheme, for the linear flux)
  regime "generic":        f'(x_i) != 0 (n_cp = 0)
  regime "critical":       with n_cp >= 1: f' = ... = f^(n_cp) = 0 at x_i and f^(n_cp + 1) != 0
  eps:                     "0", or {"c": c, "m": m}: eps = c dx^m with rational c > 0, m >= 0
Meaning: for every smooth f in the regime, E = O(dx^p) as dx -> 0 (order at least p).

Decision, exact (Fraction only). Put t = dx^(1/L), L the denominator of m. Each stencil value is a
power series in t whose coefficients are polynomials in the jet f_n = f^(n)(x_i), with
f_1 .. f_ncp = 0; the pivot f_(ncp+1) is the one entry known to be non-zero. Each
eps + beta_k = t^e_k (b_k + O(t)), and b_k must be > 0 for every jet in the regime, shown by form
(positive coefficients, even exponents, and a monomial in the pivot alone or a constant);
otherwise UNKNOWN. Multiplying every alpha_k by t^(q e_max) prod_j ((eps + beta_j) / t^e_j)^q
clears the denominators: omega_k = A_k / D, with A_k, D power series with polynomial coefficients
and D(0) > 0 (again by form). So E = N / D (point) or N / (dx D+ D-) (difference), with N a power
series in t with polynomial coefficients, and E = O(dx^p) for every jet in the regime iff the
coefficients of N below dx^p (below dx^(p+1) for the difference) are zero polynomials: a
polynomial that vanishes wherever the pivot is non-zero is zero. No rational functions and no
sampling are involved. Truncating the jet at f_K is exact for every coefficient below t^(L(K+1)),
since f_n enters only with t^(nL).
WENO-M: the map is rational in the weights, so the same clearing applies (A'_k = A_k F_k prod_{j != k} Q_j,
see _mapped); D'(0) > 0 follows from A_k(0) >= 0 by form, sum d_k = 1 and 0 < d_k < 4/5.
WENO-Z: |beta_i - beta_j| is not a power series, but for one f it equals sigma (beta_i - beta_j) for all small
dx, sigma = +1 or -1 the sign of the first non-zero term. The claim is decided in every sign branch (both
stencils for the difference: four branches), less the branches the leading term excludes by form; VERIFIED
needs every branch, and no branch is chosen by sampling. tau must be of order at least every eps + beta_k
(else UNKNOWN), which gives D(0) > 0 on each branch (see _z_weights). An even q needs no split.
REFUTED: the first non-zero coefficient of order k < p, evaluated at a concrete rational jet in the
regime where it is non-zero; the witness gives the jet, k and the dx^k coefficient of E. For WENO-Z the
jet must also lie in the branch, checked exactly: beta_i - beta_j has, at that jet, the branch's signs as
the first non-zero terms of its series (the search for such a jet may sample; the verdict then rests on the
exact check).
VERIFIED: the witness states the positivity of the b_k (by form) and the leading order found
(exact up to p + 1).
"""

from __future__ import annotations

import json
import random
import re
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

from . import cellaverage, claimkinds, eno
from .expr import E, parse

VERIFIED, REFUTED, UNKNOWN = "VERIFIED", "REFUTED", "UNKNOWN"
# the layer's claims: the order here, the cell-average step (cellaverage.py) and the ENO jump (eno.py)
CLAIMS = ("reconstruction_order_p",) + cellaverage.CLAIMS + eno.CLAIMS
claimkinds.require("reconstruction", CLAIMS)

FORMS = ("point", "flux_difference")
KINDS = ("linear", "js", "z", "m")
DATA = ("point_values", "cell_averages")
TARGETS = ("value", "primitive")
MAX_BETA_ORDER = 40  # how far, in powers of dx, to look for the leading term of eps + beta_k
BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction"


class Unknown(Exception):
    """The case is outside what the symbolic route decides."""


class _NeedCap(Exception):
    def __init__(self, cap: int):
        self.cap = cap


# ---------------------------------------------------------------- polynomials in the jet
# A polynomial is {exponent tuple: Fraction}, the tuple indexed by n for f_n. A series is a list
# of polynomials, entry j the coefficient of t^j, truncated at its length.

def padd(a: dict, b: dict, s=1) -> dict:
    out = dict(a)
    for m, c in b.items():
        v = out.get(m, 0) + s * c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def pscale(a: dict, c) -> dict:
    return {m: v * c for m, v in a.items()} if c else {}


def pmul(a: dict, b: dict) -> dict:
    out: dict = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            v = out.get(m, 0) + c1 * c2
            if v:
                out[m] = v
            else:
                del out[m]
    return out


def peval(a: dict, x) -> Fraction:
    total = Fraction(0)
    for m, c in a.items():
        for xi, k in zip(x, m):
            if k:
                c *= Fraction(xi) ** k
        total += c
    return total


def positive_by_form(a: dict, pivot: int) -> bool:
    """a > 0 for every real jet with f_pivot != 0: every coefficient positive, every exponent even,
    and one monomial in f_pivot alone (or the constant), which is then > 0."""
    return bool(a) and all(c > 0 and all(k % 2 == 0 for k in m) for m, c in a.items()) and any(
        all(k == 0 for i, k in enumerate(m) if i != pivot) for m in a)


def show(a: dict) -> str:
    if not a:
        return "0"
    terms = []
    for m, c in sorted(a.items()):
        f = "*".join(f"f{i}" + (f"^{k}" if k > 1 else "") for i, k in enumerate(m) if k)
        terms.append(str(c) if not f else f if c == 1 else f"-{f}" if c == -1 else f"{c}*{f}")
    return " + ".join(terms).replace("+ -", "- ")


def sadd(a: list, b: list, s=1) -> list:
    return [padd(x, y, s) for x, y in zip(a, b)]


def smul(a: list, b: list, n: int) -> list:
    out: list = [{} for _ in range(n)]
    for i, ai in enumerate(a[:n]):
        if ai:
            for j in range(n - i):
                if b[j]:
                    out[i + j] = padd(out[i + j], pmul(ai, b[j]))
    return out


def spow(a: list, k: int, n: int, nv: int) -> list:
    out = sconst(1, n, nv)
    for _ in range(k):
        out = smul(out, a, n)
    return out


def sconst(c, n: int, nv: int) -> list:
    return [{(0,) * nv: Fraction(c)} if c else {}] + [{} for _ in range(n - 1)]


def sshift(a: list, e: int, n: int) -> list:
    """t^e * a (e >= 0) or a / t^(-e) (dropping nothing: the caller knows the low terms vanish)."""
    if e >= 0:
        return ([{} for _ in range(e)] + a)[:n]
    return (a[-e:] + [{} for _ in range(n)])[:n]


def first_nonzero(a: list) -> int | None:
    return next((j for j, x in enumerate(a) if x), None)


# ---------------------------------------------------------------- the jet

def primitive_coefficients(n: int) -> list[Fraction]:
    """c_0..c_n of (z/2)/sinh(z/2) = sum_m c_m z^(2m), the inverse of the sliding-average symbol
    sinh(z/2)/(z/2) = sum_m z^(2m) / (4^m (2m+1)!): h^(j) = sum_m c_m dx^(2m) f^(j+2m)."""
    s = [Fraction(1, 4 ** m * factorial(2 * m + 1)) for m in range(n + 1)]
    c: list[Fraction] = []
    for m in range(n + 1):
        c.append((Fraction(int(m == 0)) - sum(s[m - i] * c[i] for i in range(m))) / s[0])
    return c


def data_weight(data: str, k: int, n: int) -> Fraction:
    """The coefficient of f_n dx^n in v_k: k^n/n! for point values, the cell average of y^n/n!
    over [k - 1/2, k + 1/2] for cell averages."""
    if data == "point_values":
        return Fraction(k) ** n / factorial(n)
    h = Fraction(1, 2)
    return ((k + h) ** (n + 1) - (k - h) ** (n + 1)) / factorial(n + 1)


def target_weight(target: str, s: Fraction, n: int) -> Fraction:
    """The coefficient of f_n dx^n in the exact value at x_i + s dx."""
    if target == "value":
        return s ** n / factorial(n)
    c = primitive_coefficients(n // 2)
    return sum((c[m] * s ** (n - 2 * m) / factorial(n - 2 * m) for m in range(n // 2 + 1)), Fraction(0))


class Jet:
    """Series in t of the stencil values and the target, with the jet truncated where exact."""

    def __init__(self, data: str, target: str, L: int, ncp: int, cap: int):
        self.data, self.target, self.L, self.ncp, self.cap = data, target, L, ncp, cap
        self.K = (cap - 1) // L
        self.nv = self.K + 1
        self._v: dict = {}

    def _series(self, weight) -> list:
        out: list = [{} for _ in range(self.cap)]
        for n in range(self.K + 1):
            if 1 <= n <= self.ncp:
                continue
            w = weight(n)
            if w:
                out[n * self.L] = {tuple(int(i == n) for i in range(self.nv)): w}
        return out

    def v(self, k: int) -> list:
        if k not in self._v:
            self._v[k] = self._series(lambda n: data_weight(self.data, k, n))
        return self._v[k]

    def exact(self, s: Fraction) -> list:
        return self._series(lambda n: target_weight(self.target, s, n))


_VAR = re.compile(r"v(m|p)?(\d+)$")


def stencil_index(name: str) -> int:
    m = _VAR.match(name)
    if not m or (m.group(1) is None) != (m.group(2) == "0"):
        raise ValueError(f"unknown stencil variable {name!r} (use v0, vm1, vp1, ...)")
    return -int(m.group(2)) if m.group(1) == "m" else int(m.group(2))


def to_series(e: E, jet: Jet, shift: int, n: int, memo: dict | None = None) -> list:
    """The expression as a series in t (length n), v_k read from the stencil shifted by `shift`."""
    memo = {} if memo is None else memo
    if id(e) in memo:
        return memo[id(e)][1]
    rec = lambda x: to_series(x, jet, shift, n, memo)
    k, a = e.kind, e.args
    if k == "var":
        out = jet.v(stencil_index(e.name) + shift)[:n]
    elif k == "lit":
        out = sconst(e.q, n, jet.nv)
    elif k == "neg":
        out = [pscale(x, -1) for x in rec(a[0])]
    elif k in ("add", "sub"):
        out = sadd(rec(a[0]), rec(a[1]), 1 if k == "add" else -1)
    elif k == "mul":
        out = smul(rec(a[0]), rec(a[1]), n)
    elif k == "powi" and e.q >= 0:
        out = spow(rec(a[0]), e.q, n, jet.nv)
    elif k == "div":
        den = rec(a[1])
        c = den[0].get((0,) * jet.nv)
        if not c or len(den[0]) != 1 or any(den[1:]):
            raise ValueError("a reconstruction formula may divide only by a non-zero constant")
        out = [pscale(x, 1 / c) for x in rec(a[0])]
    else:
        raise ValueError(f"{k} is not allowed in a reconstruction formula")
    memo[id(e)] = (e, out)
    return out


# ---------------------------------------------------------------- the spec

def parse_claim(c: dict) -> dict:
    """The claim's parameters, checked: p, form, n_cp, eps (None for eps = 0, else (c, m))."""
    p = c["p"]
    if not isinstance(p, int) or p < 0:
        raise ValueError("p must be a non-negative integer")
    form = c.get("form", "point")
    if form not in FORMS:
        raise ValueError(f"form must be one of {FORMS}")
    regime = c["regime"]
    if regime == "generic":
        ncp = 0
    elif regime == "critical":
        ncp = c["n_cp"]
        if not isinstance(ncp, int) or ncp < 1:
            raise ValueError("a critical regime needs n_cp >= 1")
    else:
        raise ValueError("regime must be 'generic' or 'critical'")
    eps = c.get("eps")
    if eps is not None and eps not in ("0", 0):
        ce, m = Fraction(str(eps["c"])), Fraction(str(eps["m"]))
        if ce <= 0 or m < 0:
            raise ValueError("eps = c dx^m needs c > 0 and m >= 0")
        eps = (ce, m)
    else:
        eps = None if eps is not None else "missing"
    return {"p": p, "form": form, "ncp": ncp, "eps": eps}


def parse_reconstruction(r: dict) -> dict:
    if r["data"] not in DATA or r["target"] not in TARGETS:
        raise ValueError(f"data must be one of {DATA}, target one of {TARGETS}")
    if r["target"] == "primitive" and r["data"] != "point_values":
        raise ValueError("the primitive target is for point values (the finite-difference flux form)")
    w = r["weights"]
    if w["kind"] not in KINDS:
        raise ValueError(f"weights kind must be one of {KINDS}")
    out = {"data": r["data"], "target": r["target"], "s": Fraction(str(r.get("point", "1/2"))),
           "q": [parse(x) for x in r["candidates"]], "d": [Fraction(str(x)) for x in w["d"]], "kind": w["kind"]}
    if len(out["d"]) != len(out["q"]):
        raise ValueError("one linear weight per candidate")
    if w["kind"] != "linear":
        out["beta"] = [parse(x) for x in w["beta"]]
        out["power"] = w["q"]
        if len(out["beta"]) != len(out["q"]) or not isinstance(w["q"], int) or w["q"] < 1:
            raise ValueError("one beta per candidate, and an integer q >= 1")
    if w["kind"] == "z":
        tau = w["tau"]
        if (not isinstance(tau, list) or len(tau) != 2 or tau[0] == tau[1]
                or any(not isinstance(i, int) or not 0 <= i < len(out["q"]) for i in tau)):
            raise ValueError("tau is [i, j], two distinct indicator indices: tau = |beta_i - beta_j|")
        out["tau"] = tuple(tau)
    return out


# ---------------------------------------------------------------- the decision

def nonneg_by_form(a: dict) -> bool:
    """a >= 0 for every real jet: zero, or every coefficient positive and every exponent even."""
    return all(c > 0 and all(k % 2 == 0 for k in m) for m, c in a.items())


def _sign_at(series: list, x: list) -> int | None:
    """The eventual sign, as dx -> 0, of a series in t at the jet x (None if every computed term is 0)."""
    for c in series:
        v = peval(c, x)
        if v:
            return 1 if v > 0 else -1
    return None


def _indicators(R: dict, jet: Jet, shift: int, n: int, eps, pivot: int, notes: list) -> tuple[list, list, list]:
    """(B, Bt, e): eps + beta_k as full series B_k = t^e_k Bt_k, Bt_k of length n with Bt_k(0) > 0 by form."""
    nv = jet.nv
    B, es = [], []
    for beta in R["beta"]:
        b = to_series(beta, jet, shift, jet.cap)
        if eps is not None:
            ce, m = eps
            j = int(m * jet.L)
            if j < jet.cap:
                b[j] = padd(b[j], {(0,) * nv: ce})
        e = first_nonzero(b)
        if e is None:
            raise _NeedCap(2 * jet.cap)
        B.append(b)
        es.append(e)
    if max(es) + n > jet.cap:
        raise _NeedCap(max(es) + n)
    Bt = [b[e:e + n] for b, e in zip(B, es)]
    for k, (b, e) in enumerate(zip(Bt, es)):
        if not positive_by_form(b[0], pivot):
            raise Unknown(f"cannot show the leading coefficient {show(b[0])} of eps + beta_{k} (stencil shift "
                          f"{shift}) is non-zero for every jet in the regime")
        notes.append(f"eps + beta_{k}{'' if shift == 0 else ' (shifted)'} = dx^{Fraction(e, jet.L)} "
                     f"({show(b[0])} + ...), > 0 by form")
    return B, Bt, es


def _weights(R: dict, jet: Jet, shift: int, n: int, eps, pivot: int, notes: list, sigma: int = 1,
             ctx: dict | None = None) -> tuple[list, list]:
    """(A_k, D) with omega_k = A_k / D, series of length n, D(0) > 0 for every jet in the regime (for WENO-Z,
    every jet of the sign branch sigma: see _z_weights)."""
    nv = jet.nv
    if R["kind"] == "linear":
        if sum(R["d"]) == 0:
            raise Unknown("the linear weights sum to 0")
        return [sconst(d, n, nv) for d in R["d"]], sconst(sum(R["d"]), n, nv)
    B, Bt, es = _indicators(R, jet, shift, n, eps, pivot, notes)
    q = R["power"]
    powers = [spow(b, q, n, nv) for b in Bt]
    if R["kind"] == "z":
        return _z_weights(R, jet, shift, n, B, es, powers, sigma, notes, ctx)
    A = []
    for k, d in enumerate(R["d"]):
        a = sconst(d, n, nv)
        for j, pw in enumerate(powers):
            if j != k:
                a = smul(a, pw, n)
        A.append(sshift(a, q * (max(es) - es[k]), n))
    D: list = [{} for _ in range(n)]
    for a in A:
        D = sadd(D, a)
    if not positive_by_form(D[0], pivot):
        raise Unknown(f"cannot show the leading coefficient {show(D[0])} of the weight denominator is non-zero")
    if R["kind"] == "m":
        return _mapped(R, A, D, n, notes)
    return A, D


def _z_weights(R: dict, jet: Jet, shift: int, n: int, B: list, es: list, powers: list, sigma: int, notes: list,
               ctx: dict | None) -> tuple[list, list]:
    """WENO-Z: alpha_k = d_k (1 + (tau / (eps + beta_k))^q), tau = |beta_i - beta_j|. Times the common positive
    factor prod_j Bt_j^q: A_k = d_k (Bt_k^q + (tau / t^e_k)^q) prod_{j != k} Bt_j^q.

    The absolute value. Delta = beta_i - beta_j is a series in t (eps cancels). For one smooth f, Delta(dx)
    has the sign of its first non-zero term for all small dx, so there |Delta| = sigma Delta with sigma = +1
    or -1; if every term is zero, both signs give the same series. The caller decides both branches and
    picks none of them by sampling. In a branch, tau = sigma Delta is a series with polynomial coefficients.
    If Delta = O(dx^e) with e at least every e_k, then tau / t^e_k is a power series and
    D(0) = sum_k d_k (Bt_k(0)^q + [e = e_k] (sigma delta)^q) prod_{j != k} Bt_j(0)^q
         >= (sum_k d_k) prod_j Bt_j(0)^q > 0
    for every jet of the branch, delta being the dx^e coefficient of Delta (sigma delta >= 0 on the branch,
    as either delta = 0 there or its sign is the eventual sign of Delta)."""
    nv, q = jet.nv, R["power"]
    i, j = R["tau"]
    if any(d <= 0 for d in R["d"]):
        raise Unknown("WENO-Z needs every linear weight d_k > 0")
    delta = sadd(B[i], B[j], -1)
    e_d = first_nonzero(delta)
    if ctx is not None:
        ctx.setdefault("delta", {})[shift] = delta
    if e_d is not None and e_d < max(es):
        raise Unknown(f"tau = |beta_{i} - beta_{j}| = O(dx^{Fraction(e_d, jet.L)}) is not small against every "
                      f"eps + beta_k (largest order dx^{Fraction(max(es), jet.L)})")
    tag = "" if shift == 0 else " (shifted)"
    if e_d is None:
        notes.append(f"beta_{i} - beta_{j}{tag} has no non-zero term below dx^{Fraction(jet.cap, jet.L)}")
    else:
        notes.append(f"beta_{i} - beta_{j}{tag} = dx^{Fraction(e_d, jet.L)} ({show(delta[e_d])} + ...), of order at "
                     f"least that of every eps + beta_k, so D(0) >= (sum d_k) prod_j Bt_j(0)^q > 0 in each sign branch")
    tau = [pscale(c, sigma) for c in delta]
    A = []
    for k, d in enumerate(R["d"]):
        a = sadd(powers[k], spow(sshift(tau, -es[k], n), q, n, nv))
        a = [pscale(c, d) for c in a]
        for jj, pw in enumerate(powers):
            if jj != k:
                a = smul(a, pw, n)
        A.append(a)
    D: list = [{} for _ in range(n)]
    for a in A:
        D = sadd(D, a)
    return A, D


def _mapped(R: dict, A: list, D: list, n: int, notes: list) -> tuple[list, list]:
    """WENO-M (Henrick, Aslam and Powers): w_k = A_k / D mapped by
    g_k(w) = w (d_k + d_k^2 - 3 d_k w + w^2) / (d_k^2 + w (1 - 2 d_k)), then renormalised. With w = A / D,
    g_k = A_k F_k / (D^2 Q_k), where F_k = d (1 + d) D^2 - 3 d A_k D + A_k^2 and
    Q_k = d^2 D + (1 - 2d) A_k = d^2 (D - A_k) + (1 - d)^2 A_k, so the mapped weights are A'_k / D' with
    A'_k = A_k F_k prod_{j != k} Q_j and D' = sum_k A'_k: rational again, cleared the same way.
    D'(0) > 0 for every jet: each A_k(0) >= 0 by form and sum_k A_k(0) = D(0) > 0; F_k(0) > 0 since the
    form d (1 + d) X^2 - 3 d X Y + Y^2 is positive definite for 0 < d < 4/5 and D(0) != 0; and
    Q_k(0) >= min(d^2, (1 - d)^2) D(0) > 0."""
    d = R["d"]
    if sum(d) != 1 or any(not 0 < x < Fraction(4, 5) for x in d):
        raise Unknown("the mapping is decided for linear weights with sum 1 and 0 < d_k < 4/5")
    if not all(nonneg_by_form(a[0]) for a in A):
        raise Unknown("cannot show every leading weight numerator A_k(0) >= 0 by form")
    DD = smul(D, D, n)
    F, Q = [], []
    for a, dk in zip(A, d):
        f = sadd([pscale(c, dk * (1 + dk)) for c in DD], [pscale(c, -3 * dk) for c in smul(a, D, n)])
        F.append(sadd(f, smul(a, a, n)))
        Q.append(sadd([pscale(c, dk * dk) for c in sadd(D, a, -1)], [pscale(c, (1 - dk) ** 2) for c in a]))
    A2 = []
    for k, a in enumerate(A):
        x = smul(a, F[k], n)
        for j, qj in enumerate(Q):
            if j != k:
                x = smul(x, qj, n)
        A2.append(x)
    D2: list = [{} for _ in range(n)]
    for a in A2:
        D2 = sadd(D2, a)
    notes.append("mapped weights: D'(0) > 0, since every A_k(0) >= 0 by form, sum_k A_k(0) = D(0) > 0, "
                 "sum d_k = 1 and 0 < d_k < 4/5")
    return A2, D2


def _numerator(R: dict, jet: Jet, shift: int, n: int, eps, pivot: int, notes: list, sigma: int = 1,
               ctx: dict | None = None) -> tuple[list, list]:
    """(N, D) with R - T = N / D at the stencil shifted by `shift` (evaluation point s + shift)."""
    A, D = _weights(R, jet, shift, n, eps, pivot, notes, sigma, ctx)
    N = smul([pscale(x, -1) for x in jet.exact(R["s"] + shift)[:n]], D, n)
    for a, qk in zip(A, R["q"]):
        N = sadd(N, smul(a, to_series(qk, jet, shift, n), n))
    return N, D


def _split(R: dict) -> bool:
    """Only WENO-Z with an odd power needs the sign of beta_i - beta_j (an even power squares it away)."""
    return R["kind"] == "z" and R["power"] % 2 == 1


def _branches(R: dict, jet: Jet, form: str, pivot: int) -> list[tuple]:
    """The sign branches (sigma at x_{i+1/2}[, sigma at x_{i-1/2}]), less those the leading term of
    beta_i - beta_j excludes by form (its sign fixed for every jet in the regime)."""
    shifts = (0,) if form == "point" else (0, -1)
    if not _split(R):
        return [(1,) * len(shifts)]
    i, j = R["tau"]
    allowed = []
    for s in shifts:
        delta = sadd(to_series(R["beta"][i], jet, s, jet.cap), to_series(R["beta"][j], jet, s, jet.cap), -1)
        e = first_nonzero(delta)
        signs = [g for g in (1, -1) if e is None or not positive_by_form(pscale(delta[e], -g), pivot)]
        allowed.append(signs)
    return [(a,) for a in allowed[0]] if form == "point" else [(a, b) for a in allowed[0] for b in allowed[1]]


def _branch_label(R: dict, sig: tuple) -> str:
    i, j = R["tau"]
    return ", ".join(f"beta_{i} - beta_{j} {'>' if g > 0 else '<'} 0 at {at}"
                     for g, at in zip(sig, ("x_{i+1/2}", "x_{i-1/2}")))


def decide(R: dict, C: dict) -> dict:
    """The verdict of one claim on one parsed reconstruction (see the module docstring)."""
    p, form, ncp, eps = C["p"], C["form"], C["ncp"], C["eps"]
    if R["kind"] != "linear" and eps == "missing":
        raise ValueError(f"a {R['kind']} claim must name its eps scaling ('0' or {{c, m}})")
    if R["kind"] == "linear":
        eps = None
    L = eps[1].denominator if eps else 1
    pivot = ncp + 1
    n = (p + 1) * L if form == "point" else (p + 2) * L  # t^0 .. through dx^p of E
    cap = n + 8 * L
    while True:
        if cap > (MAX_BETA_ORDER + p + 2) * L:
            return {"verdict": UNKNOWN, "reason": f"eps + beta_k has no non-zero term up to dx^{MAX_BETA_ORDER}"}
        jet, notes, ctx = Jet(R["data"], R["target"], L, ncp, cap), [], {}
        try:
            branches = []
            for sig in _branches(R, jet, form, pivot):
                Np, Dp = _numerator(R, jet, 0, n, eps, pivot, notes, sig[0], ctx)
                if form == "point":
                    branches.append((sig, Np, [Dp]))
                else:
                    Nm, Dm = _numerator(R, jet, -1, n, eps, pivot, notes, sig[1], ctx)
                    branches.append((sig, sadd(smul(Np, Dm, n), smul(Nm, Dp, n), -1), [Dp, Dm]))
            break
        except _NeedCap as e:
            cap = max(e.cap, cap + L)
        except Unknown as e:
            return {"verdict": UNKNOWN, "reason": str(e)}
    shift = 0 if form == "point" else 1  # E = N / D or N / (dx D+ D-)
    orders = []
    for _, N, _ in branches:
        j0 = first_nonzero(N)
        orders.append(None if j0 is None else Fraction(j0, L) - shift)
    known = [o for o in orders if o is not None]
    out = {"jet_order": jet.K, "assumptions": list(dict.fromkeys(notes)),
           "leading_order": str(min(known)) if known else f">= {p + 1}"}
    if _split(R):
        out["branch_orders"] = {_branch_label(R, sig): str(o) if o is not None else f">= {p + 1}"
                                for (sig, _, _), o in zip(branches, orders)}
    if all(o is None or o >= p for o in orders):
        coeffs = f"dx^0 .. dx^{p - 1}" if p else "none (p = 0)"
        where = " in every sign branch of tau" if _split(R) else ""
        out.update(verdict=VERIFIED, reason=f"the coefficients of {coeffs} of E vanish identically in the jet "
                   f"(f_1..f_{ncp} = 0, f_{pivot} != 0, the others free){where}, given the positive leading terms")
        return out
    low = sorted((o, b) for b, o in enumerate(orders) if o is not None and o < p)
    for o, b in low:
        sig, N, Ds = branches[b]
        j0 = first_nonzero(N)
        accept = None
        if _split(R):
            def accept(x, sig=sig):
                return all(_sign_at(ctx["delta"][s], x) == g for s, g in zip((0, -1), sig))
        try:
            jet_vals, d0 = concrete_jet(N[j0], [D[0] for D in Ds], pivot, jet.nv, ncp, accept)
        except Unknown:
            continue
        coef = peval(N[j0], jet_vals) / d0
        used = max([i for mono in N[j0] for i, k in enumerate(mono) if k] + [pivot])
        reason = f"for this jet the error is {coef} dx^{o} + o(dx^{o}), and {o} < {p}"
        if _split(R):  # the branch depends on the whole computed jet: report all of it
            used = jet.K
            out["branch"] = _branch_label(R, sig)
            reason += " (the jet lies in this sign branch: there beta_i - beta_j has these eventual signs)"
        out.update(verdict=REFUTED, k=str(o), coefficient=str(coef),
                   jet={f"f^({i})": str(jet_vals[i]) for i in range(used + 1)}, reason=reason)
        return out
    out.update(verdict=UNKNOWN, reason=f"order {low[0][0]} < {p} in a sign branch of tau, but no rational jet "
               "of that branch was found to exhibit it")
    return out


def concrete_jet(poly: dict, dens: list, pivot: int, nv: int, ncp: int, accept=None) -> tuple[list, Fraction]:
    """A rational jet in the regime where `poly` is non-zero (it is a non-zero polynomial) and `accept` holds,
    with the product of the denominators' leading terms (all > 0 there)."""
    first = [Fraction(0)] + [Fraction(0)] * ncp + [Fraction(1)] + [Fraction(1, i) for i in range(2, nv - ncp)]
    tries = [first[:nv]]
    rnd = random.Random(0)
    vals = [Fraction(x) for x in (-2, -1, Fraction(-1, 2), Fraction(1, 2), 1, 2, 3)]
    for _ in range(500):
        x = [rnd.choice(vals) for _ in range(nv)]
        for i in range(1, ncp + 1):
            x[i] = Fraction(0)
        tries.append(x)
    for x in tries:
        if peval(poly, x) and (accept is None or accept(x)):
            d0 = Fraction(1)
            for d in dens:
                d0 *= peval(d, x)
            if d0 <= 0:
                raise Unknown(f"a weight denominator is not positive at the jet {x}, against the argument above")
            return x, d0
    raise Unknown("no rational jet found where the leading error coefficient is non-zero")


def check_claim(rec: dict, claim: dict) -> dict:
    for mod in (cellaverage, eno):
        if claim.get("claim") in mod.CLAIMS:
            return mod.check_claim(rec, claim)
    try:
        R, C = parse_reconstruction(rec), parse_claim(claim)
    except (KeyError, ValueError) as e:
        return {"verdict": UNKNOWN, "reason": f"bad spec: {e}"}
    return decide(R, C)


def check(spec: dict) -> dict:
    """{"claims": [one result per claim of the spec, with "claim" and "verdict"]}."""
    out = []
    for c in spec["claims"]:
        r = check_claim(spec["reconstruction"], c) if c["claim"] in CLAIMS else {
            "verdict": UNKNOWN, "reason": f"unknown claim {c['claim']}"}
        out.append({"claim": c["claim"], **r})
    return {"claims": out}


# ---------------------------------------------------------------- direct evaluation

def _eval(e: E, env: dict) -> Fraction:
    k, a = e.kind, e.args
    if k == "var": return env[stencil_index(e.name)]
    if k == "lit": return e.q
    if k == "neg": return -_eval(a[0], env)
    if k == "add": return _eval(a[0], env) + _eval(a[1], env)
    if k == "sub": return _eval(a[0], env) - _eval(a[1], env)
    if k == "mul": return _eval(a[0], env) * _eval(a[1], env)
    if k == "div": return _eval(a[0], env) / _eval(a[1], env)
    if k == "powi": return _eval(a[0], env) ** e.q
    raise ValueError(k)


def direct_error(rec: dict, claim: dict, jet: list, t: Fraction) -> Fraction:
    """E exactly at dx = t^L for the polynomial f(x_i + y) = sum_n jet[n] y^n / n!, by plain
    evaluation of the formulas (no series): the independent check of a witness."""
    R, C = parse_reconstruction(rec), parse_claim(claim)
    eps = C["eps"] if R["kind"] != "linear" else None
    L = eps[1].denominator if eps else 1
    dx = Fraction(t) ** L
    epsv = eps[0] * t ** int(eps[1] * L) if eps else Fraction(0)
    K = len(jet) - 1
    cprim = primitive_coefficients(K // 2)

    def recon(shift: int) -> Fraction:
        v = {}
        for k in range(-6, 7):
            v[k] = sum((Fraction(jet[n]) * data_weight(R["data"], k + shift, n) * dx ** n for n in range(K + 1)),
                       Fraction(0))
        qs = [_eval(q, v) for q in R["q"]]
        if R["kind"] == "linear":
            w = list(R["d"])
        elif R["kind"] == "z":
            bs = [_eval(b, v) for b in R["beta"]]
            tau = abs(bs[R["tau"][0]] - bs[R["tau"][1]])
            w = [d * (1 + (tau / (epsv + b)) ** R["power"]) for d, b in zip(R["d"], bs)]
        else:
            w = [d / (epsv + _eval(b, v)) ** R["power"] for d, b in zip(R["d"], R["beta"])]
            if R["kind"] == "m":
                w = [x / sum(w) for x in w]
                w = [x * (d + d * d - 3 * d * x + x * x) / (d * d + x * (1 - 2 * d)) for x, d in zip(w, R["d"])]
        s = R["s"] + shift
        if R["target"] == "value":
            exact = sum((Fraction(jet[n]) * (s * dx) ** n / factorial(n) for n in range(K + 1)), Fraction(0))
        else:  # h = sum_m c_m dx^2m f^(2m) as a polynomial, evaluated at s dx
            exact = sum((cprim[m] * dx ** (2 * m) * Fraction(jet[j + 2 * m]) * (s * dx) ** j / factorial(j)
                         for j in range(K + 1) for m in range((K - j) // 2 + 1)), Fraction(0))
        return sum((wk * qk for wk, qk in zip(w, qs)), Fraction(0)) / sum(w) - exact

    if C["form"] == "point":
        return recon(0)
    return (recon(0) - recon(-1)) / dx


# ---------------------------------------------------------------- the bench table

def _eps_label(c: dict) -> str:
    e = c.get("eps")
    if e is None:
        return "-"
    return "0" if e in ("0", 0) else f"{e['c']}*dx^{e['m']}"


def main(argv=None) -> int:
    paths = []
    for a in (argv if argv is not None else sys.argv[1:]) or [str(BENCH)]:
        p = Path(a)
        paths += sorted(p.glob("*.json")) if p.is_dir() else [p]
    print("| spec | form | regime | eps | p | expected | verdict | leading order |\n|---|---|---|---|---|---|---|---|")
    wrong = unsure = 0
    for path in paths:
        spec = json.loads(path.read_text())
        for c, r in zip(spec["claims"], check(spec)["claims"]):
            ok = r["verdict"] == c.get("expect")
            flag = "" if ok else ("  (UNSURE, differs)" if c.get("confidence") == "unsure" else "  (WRONG)")
            wrong += not ok and c.get("confidence") != "unsure"
            unsure += not ok and c.get("confidence") == "unsure"
            regime = c["regime"] + (f" n_cp={c['n_cp']}" if c["regime"] == "critical" else "")
            lead = r.get("leading_order", r.get("reason", ""))
            print(f"| {path.stem} | {c.get('form', 'point')} | {regime} | {_eps_label(c)} | {c['p']} | "
                  f"{c.get('expect')} | {r['verdict']}{flag} | {lead} |")
    print(f"\n{wrong} not as expected, {unsure} unsure expectations differ")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
