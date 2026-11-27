"""Maximum principle of one cell-average step fed by polynomials (claim kind `cell_average_max_principle`),
decided exactly.

Usage: python -m physverify.cellaverage [paths]   (by default benchmark/reconstruction/cell-average)

A spec (benchmark/reconstruction/cell-average/*.json) holds polynomials p_c of degree <= k, one per cell c, in the
local coordinate y in [-1/2, 1/2] of the cell. `values` names linear functionals of them: [c, y] is p_c(y) and
[c, "avg"] is the cell average of p_c. `update` is the new cell average, linear in the named values, with
coefficients polynomial in lam = dt/dx (no constant term). `hypotheses` are linear combinations of the named values
with constant coefficients.

Claim: for every lam in [lo, hi], all such polynomials and all m <= M, if every hypothesis lies in [m, M], so does
the update.

Decision. Every functional is a vector on the coefficients of the polynomials (monomials y^n, n <= k, per cell): the
update U(lam), the hypotheses H_1..H_r. If U(lam) and every H_i give 1 on the constant data p_c = 1 (U(lam)(1) = 1
identically in lam), the claim is equivalent, for each lam, to U(lam) = sum_i mu_i H_i with mu_i >= 0 (sufficiency:
a convex combination; necessity: LP duality on the polyhedron {m <= H_i <= M}, since U(1) = H_i(1) = 1 forces the
dual weights of the lower bounds to vanish when m < M). A hypothesis that is a non-negative constant combination of
the hypotheses before it adds nothing and is dropped (e.g. the average, Simpson's combination of the Gauss–Lobatto
values for k <= 3); the rest must be linearly independent (else UNKNOWN), so the mu_i(lam) are unique polynomials.
Then:
  VERIFIED  if U(lam) lies in their span identically and every mu_i(lam) >= 0 on [lo, hi]
            (physverify.schemes.univariate.nonneg_on: square-free decomposition and Sturm counts, exact);
  REFUTED   with an explicit datum: at a rational lam0 in [lo, hi] where some mu_i(lam0) < 0, polynomials with
            H_i = 0 where mu_i(lam0) < 0 and H_i = 1 elsewhere (solved exactly), whose update is
            1 - sum_{mu_i < 0} mu_i > 1, or, if U(lam0) is outside the span, a datum with every H_i = 1/2 and update
            > 1. The witness is checked by direct evaluation of the formulas (every hypothesis in [0, 1], update
            outside).
Fraction arithmetic only; nothing is sampled.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

from . import claimkinds
from .expr import E, parse
from .schemes import univariate as U

VERIFIED, REFUTED, UNKNOWN = "VERIFIED", "REFUTED", "UNKNOWN"
CLAIMS = ("cell_average_max_principle",)
claimkinds.require("reconstruction", CLAIMS)
BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "cell-average"
LAM = "lam"


class Unknown(Exception):
    pass


# ---------------------------------------------------------------- linear forms
# A form is {name: poly in lam (list of Fractions, constant first)}; the constant term is under the key None.

def _fadd(a: dict, b: dict, s=1) -> dict:
    out = dict(a)
    for k, p in b.items():
        out[k] = U.add(out.get(k, []), p, s)
        if not out[k]:
            del out[k]
    return out


def _fscale(a: dict, p: list) -> dict:
    return {k: q for k, v in a.items() if (q := U.mul(v, p))}


def linear_form(e: E, names: set) -> dict:
    """The expression as a linear form in `names`, with coefficients polynomial in lam."""
    k, a = e.kind, e.args
    if k == "var":
        if e.name == LAM:
            return {None: [Fraction(0), Fraction(1)]}
        if e.name not in names:
            raise ValueError(f"unknown value {e.name!r}")
        return {e.name: [Fraction(1)]}
    if k == "lit":
        return {None: [Fraction(e.q)]} if e.q else {}
    if k == "neg":
        return _fscale(linear_form(a[0], names), [Fraction(-1)])
    if k in ("add", "sub"):
        return _fadd(linear_form(a[0], names), linear_form(a[1], names), 1 if k == "add" else -1)
    if k == "mul":
        x, y = linear_form(a[0], names), linear_form(a[1], names)
        for p, q in ((x, y), (y, x)):
            if set(p) <= {None}:
                return _fscale(q, p.get(None, []))
        raise ValueError("the update must be linear in the values")
    if k == "div":
        y = linear_form(a[1], names)
        if set(y) != {None} or len(y[None]) != 1:
            raise ValueError("divide only by a non-zero constant")
        return _fscale(linear_form(a[0], names), [1 / y[None][0]])
    if k == "powi" and e.q >= 0:
        x = linear_form(a[0], names)
        if set(x) <= {None}:
            return {None: U.power(x.get(None, []), e.q)} if x else {}
        if e.q == 1:
            return x
    raise ValueError(f"{k} is not allowed in an update")


# ---------------------------------------------------------------- the polynomial data

def functional(where: list, k: int, cells: list) -> list[Fraction]:
    """The value [c, y] or [c, "avg"] as a vector on the monomial coefficients of all cells."""
    c, y = where
    vec = [Fraction(0)] * (len(cells) * (k + 1))
    base = cells.index(c) * (k + 1)
    for n in range(k + 1):
        if y == "avg":
            vec[base + n] = Fraction(1, (n + 1) * 2 ** n) if n % 2 == 0 else Fraction(0)  # int y^n over [-1/2, 1/2]
        else:
            vec[base + n] = Fraction(str(y)) ** n
    return vec


def _combine(form: dict, vecs: dict, dim: int) -> list[list]:
    """A form of names -> one poly in lam per coordinate."""
    out = [[] for _ in range(dim)]
    for name, p in form.items():
        for j, v in enumerate(vecs[name]):
            if v:
                out[j] = U.add(out[j], [x * v for x in p])
    return out


def solve(rows: list[list[Fraction]], rhs: list):
    """Coefficients x with sum_i x_i rows[i] = rhs, rows independent; rhs entries are Fractions or polys in lam.
    Returns (x, residual): x_i polys, residual the part of rhs outside the span (polys, all [] if inside)."""
    r, dim = len(rows), len(rows[0]) if rows else 0
    # Gaussian elimination on the transposed system: columns = rows
    A = [[rows[i][j] for i in range(r)] for j in range(dim)]
    b = [x if isinstance(x, list) else ([x] if x else []) for x in rhs]
    piv_cols, row = [], 0
    for col in range(r):
        p = next((i for i in range(row, dim) if A[i][col] != 0), None)
        if p is None:
            raise Unknown("the hypotheses are linearly dependent")
        A[row], A[p], b[row], b[p] = A[p], A[row], b[p], b[row]
        inv = 1 / A[row][col]
        A[row] = [v * inv for v in A[row]]
        b[row] = [v * inv for v in b[row]]
        for i in range(dim):
            if i != row and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[row])]
                b[i] = U.add(b[i], [f * v for v in b[row]], -1)
        piv_cols.append(col)
        row += 1
    return [U.trim(b[i]) for i in range(r)], [U.trim(b[i]) for i in range(r, dim)]


def rank_independent(rows: list[list[Fraction]]) -> bool:
    try:
        solve(rows, [Fraction(0)] * len(rows[0]))
        return True
    except Unknown:
        return False


def _point_solution(rows: list[list[Fraction]], targets: list[Fraction]) -> list[Fraction]:
    """A coefficient vector c with rows[i] . c = targets[i] (rows independent): free coordinates set to 0."""
    r, dim = len(rows), len(rows[0])
    A = [list(rw) + [t] for rw, t in zip(rows, targets)]
    piv, row = [], 0
    for col in range(dim):
        p = next((i for i in range(row, r) if A[i][col] != 0), None)
        if p is None:
            continue
        A[row], A[p] = A[p], A[row]
        inv = 1 / A[row][col]
        A[row] = [v * inv for v in A[row]]
        for i in range(r):
            if i != row and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[row])]
        piv.append(col)
        row += 1
        if row == r:
            break
    c = [Fraction(0)] * dim
    for i, col in enumerate(piv):
        c[col] = A[i][dim]
    return c


def _dot(a: list, c: list) -> Fraction:
    return sum((x * y for x, y in zip(a, c)), Fraction(0))


def parse_spec(rec: dict) -> dict:
    k = rec["degree"]
    if not isinstance(k, int) or k < 0:
        raise ValueError("degree must be a non-negative integer")
    values = rec["values"]
    if LAM in values:
        raise ValueError(f"{LAM!r} is reserved for dt/dx")
    cells = sorted({w[0] for w in values.values()})
    if any(not isinstance(c, int) for c in cells):
        raise ValueError("a value is [cell offset, y] or [cell offset, 'avg']")
    for w in values.values():
        if w[1] != "avg" and abs(Fraction(str(w[1]))) > Fraction(1, 2):
            raise ValueError("points lie in the cell, y in [-1/2, 1/2]")
    vecs = {n: functional(w, k, cells) for n, w in values.items()}
    dim = len(cells) * (k + 1)
    upd = linear_form(parse(rec["update"]), set(values))
    if None in upd:
        raise ValueError("the update has a constant term")
    hyps = []
    for h in rec["hypotheses"]:
        f = linear_form(parse(h), set(values))
        if None in f or any(len(p) > 1 for p in f.values()):
            raise ValueError("a hypothesis is a combination of values with constant coefficients")
        hyps.append((h, [p[0] if p else Fraction(0) for p in _combine(f, vecs, dim)]))
    return {"k": k, "cells": cells, "dim": dim, "update": _combine(upd, vecs, dim), "hyps": hyps}


def decide(S: dict, lo: Fraction, hi: Fraction) -> dict:
    k, cells, dim, upd = S["k"], S["cells"], S["dim"], S["update"]
    ones = [Fraction(0)] * dim  # p_c = 1 in every cell
    for i in range(len(cells)):
        ones[i * (k + 1)] = Fraction(1)
    u1 = [Fraction(0)]
    for j in range(dim):
        u1 = U.add(u1, [x * ones[j] for x in upd[j]])
    if U.trim(U.add(u1, [Fraction(1)], -1)):
        raise Unknown(f"the update is not 1 on constant data (it is {U.show(u1, LAM)}): the claim is not "
                      "decided by convex combinations")
    for name, h in S["hyps"]:
        if _dot(h, ones) != 1:
            raise Unknown(f"the hypothesis {name} is not 1 on constant data")
    kept, dropped = [], []
    for name, h in S["hyps"]:
        if kept:
            try:
                coef, res = solve([x for _, x in kept], h)
            except Unknown:
                raise Unknown("the hypotheses kept so far are linearly dependent")
            if not any(res):
                if all(not c or (len(c) == 1 and c[0] >= 0) for c in coef):
                    dropped.append({"hypothesis": name, "as": {kn: str(c[0]) for (kn, _), c in zip(kept, coef) if c}})
                    continue
                raise Unknown(f"the hypothesis {name} is a combination of the others with a negative weight: "
                              "the decision needs a linear programme, not done")
        kept.append((name, h))
    rows = [h for _, h in kept]
    mu, res = solve(rows, upd)
    out = {"kept": [n for n, _ in kept], "dropped": dropped,
           "weights": {n: U.show(m, LAM) for (n, _), m in zip(kept, mu)}}
    if any(res):
        lam0 = lo if lo == hi else _outside_point(res, lo, hi)
        return _refute_outside(S, rows, lam0, out)
    certs = {}
    for (n, _), m in zip(kept, mu):
        r = U.nonneg_on(m, lo, hi)
        if not r["nonneg"]:
            lam0 = r["counterexample"]["x"]
            return _refute_negative(S, rows, mu, lam0, out, n)
        certs[n] = r["certificate"]["method"]
    out.update(verdict=VERIFIED, reason=f"the update is sum_i mu_i(lam) H_i, an identity in the polynomial "
               f"coefficients, with every mu_i(lam) >= 0 on [{lo}, {hi}] (exact: {sorted(set(certs.values()))}) "
               "and sum_i mu_i = 1: a convex combination of the hypotheses")
    return out


def _outside_point(res: list, lo: Fraction, hi: Fraction) -> Fraction:
    for x in (lo, hi, (lo + hi) / 2):
        if any(U.ev(p, x) for p in res):
            return x
    n = 3
    while True:  # a non-zero polynomial has finitely many roots: some grid point of [lo, hi] avoids them
        for i in range(1, n):
            x = lo + (hi - lo) * Fraction(i, n)
            if any(U.ev(p, x) for p in res):
                return x
        n += 1


def _evaluate(S: dict, lam0: Fraction, c: list) -> tuple[Fraction, list]:
    return (_dot([U.ev(p, lam0) for p in S["update"]], c), [(n, _dot(h, c)) for n, h in S["hyps"]])


def _witness(S: dict, c: list, lam0: Fraction, out: dict, why: str) -> dict:
    u, hs = _evaluate(S, lam0, c)
    if not (all(0 <= v <= 1 for _, v in hs) and (u > 1 or u < 0)):
        raise AssertionError("the constructed datum does not refute the claim")
    k = S["k"]
    polys = {str(cell): " + ".join(f"{c[i * (k + 1) + n]}*y^{n}" for n in range(k + 1))
             for i, cell in enumerate(S["cells"])}
    out.update(verdict=REFUTED, lam=str(lam0), m="0", M="1", polynomials=polys,
               hypothesis_values={n: str(v) for n, v in hs}, update_value=str(u),
               reason=f"{why}; at lam = {lam0}, with these polynomials every hypothesis is in [0, 1] and the "
                      f"update is {u} (checked by direct evaluation)")
    return out


def _refute_negative(S, rows, mu, lam0, out, name) -> dict:
    targets = [Fraction(0) if U.ev(m, lam0) < 0 else Fraction(1) for m in mu]
    c = _point_solution(rows, targets)
    return _witness(S, c, lam0, out, f"the weight of {name} is {U.ev(mu[out['kept'].index(name)], lam0)} < 0")


def _refute_outside(S, rows, lam0, out) -> dict:
    """U(lam0) is not in the span of the hypotheses: move along a direction the hypotheses do not see."""
    base = _point_solution(rows, [Fraction(1, 2)] * len(rows))
    u_vec = [U.ev(p, lam0) for p in S["update"]]
    dim = S["dim"]
    for j in range(dim):  # a kernel vector of the rows with u . v != 0: complete e_j by the rows
        e = [Fraction(int(i == j)) for i in range(dim)]
        corr = _point_solution(rows, [_dot(r, e) for r in rows])
        v = [a - b for a, b in zip(e, corr)]
        if any(_dot(r, v) for r in rows):
            continue
        d = _dot(u_vec, v)
        if d:
            t = (2 - _dot(u_vec, base)) / d  # update = 2
            c = [a + t * b for a, b in zip(base, v)]
            return _witness(S, c, lam0, out, "the update is not a combination of the hypotheses")
    raise Unknown("no direction found outside the span (against the residual)")


def check_claim(rec: dict, claim: dict) -> dict:
    try:
        S = parse_spec(rec)
        lo, hi = (Fraction(str(x)) for x in claim["lam"])
        if lo > hi or lo < 0:
            raise ValueError("lam = [lo, hi] with 0 <= lo <= hi")
    except (KeyError, ValueError, TypeError) as e:
        return {"verdict": UNKNOWN, "reason": f"bad spec: {e}"}
    try:
        return decide(S, lo, hi)
    except Unknown as e:
        return {"verdict": UNKNOWN, "reason": str(e)}


def check(spec: dict) -> dict:
    out = []
    for c in spec["claims"]:
        r = check_claim(spec["reconstruction"], c) if c["claim"] in CLAIMS else {
            "verdict": UNKNOWN, "reason": f"unknown claim {c['claim']}"}
        out.append({"claim": c["claim"], **r})
    return {"claims": out}


def main(argv=None) -> int:
    paths = []
    for a in (argv if argv is not None else sys.argv[1:]) or [str(BENCH)]:
        p = Path(a)
        paths += sorted(p.glob("*.json")) if p.is_dir() else [p]
    print("| spec | lam | expected | verdict | weights |\n|---|---|---|---|---|")
    wrong = unsure = 0
    for path in paths:
        spec = json.loads(path.read_text())
        for c, r in zip(spec["claims"], check(spec)["claims"]):
            ok = r["verdict"] == c.get("expect")
            flag = "" if ok else ("  (UNSURE, differs)" if c.get("confidence") == "unsure" else "  (WRONG)")
            wrong += not ok and c.get("confidence") != "unsure"
            unsure += not ok and c.get("confidence") == "unsure"
            w = ", ".join(f"{n}: {v}" for n, v in r.get("weights", {}).items()) or r.get("reason", "")
            print(f"| {path.stem} | [{c['lam'][0]}, {c['lam'][1]}] | {c.get('expect')} | {r['verdict']}{flag} | {w} |")
    print(f"\n{wrong} not as expected, {unsure} unsure expectations differ")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
