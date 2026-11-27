"""Sign property and jump bound of ENO interpolation of point values, for all data (claim kinds
`eno_sign_property`, `eno_jump_ratio_at_most`), decided exactly.

Usage: python -m physverify.eno [paths]   (by default benchmark/reconstruction/eno)

A spec gives the order k (stencils of k points) and the stencil selection: `"eno"` with `"tie": "left"|"right"`,
or `{"fixed": r}`, the stencil {i - r, ..., i - r + k - 1} for every cell i. ENO grows the stencil of cell i from
{i}: from {a..b} it compares the undivided differences A of w on {a-1..b} and B of w on {a..b+1} and takes the
left one if |A| < |B|, the right one if |A| > |B|, and on |A| = |B| the side of the tie rule. w^+_i is the
interpolant of the stencil of cell i at x_{i+1/2}, w^-_{i+1} that of cell i + 1 at the same point; the jump is
J = w^-_{i+1} - w^+_i and the difference D = w_{i+1} - w_i.

Claims, over every real data vector (w_{i-k+1}, ..., w_{i+k}):
  eno_sign_property       J D >= 0, and J = 0 where D = 0 (the weak form; the strict sign(J) = sign(D) fails for
                          every k >= 2 on linear data, where J = 0 and D != 0)
  eno_jump_ratio_at_most  J / D <= c wherever D != 0

Decision. Put i = 0; J, D and every undivided difference are linear forms in w, invariant under adding a constant,
so w_0 = 0 is fixed. The selection of each cell is a path of k - 1 choices, each holding on |A| <= |B| (or <, by
the tie rule) or its complement, and |A| <= |B| is the union of the two cones {B - A >= 0, B + A >= 0} and
{B - A <= 0, B + A <= 0} (strict for <). So the data space is covered by finitely many polyhedral branches (two
cells, 4^(k-1) each), on each of which J and D are fixed linear forms. A claim fails iff one of finitely many systems
of linear inequalities, strict and non-strict (a branch and, e.g., D > 0, J < 0), has a real solution. Each
system is decided by Fourier–Motzkin elimination over the rationals, which tracks strictness exactly: infeasible
iff some derived constraint reads 0 > 0 or 0 >= b > 0.
  VERIFIED   every failing system is infeasible (the witness counts the branches and systems);
  REFUTED    a rational solution of a failing system, by back-substitution, then checked by direct evaluation:
             the ENO choices recomputed from w with plain comparisons, J and D evaluated, the claim seen to fail.
For the ratio, the witness also reports sup J / D over every branch (the maximum of J on the closure of
branch and D = 1, by elimination), exact. Fraction arithmetic only; nothing is sampled.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path

from . import claimkinds

VERIFIED, REFUTED, UNKNOWN = "VERIFIED", "REFUTED", "UNKNOWN"
CLAIMS = ("eno_sign_property", "eno_jump_ratio_at_most")
claimkinds.require("reconstruction", CLAIMS)
BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "eno"
MAX_ORDER = 3  # k = 4 has 4^6 branch pairs and the elimination takes minutes: UNKNOWN beyond


# ---------------------------------------------------------------- linear forms on the data
# The data are w_j, j = -k+1 .. k; a form is a tuple of Fractions indexed by j + k - 1.

class Grid:
    def __init__(self, k: int):
        self.k, self.n = k, 2 * k
        self.idx = list(range(-k + 1, k + 1))

    def unit(self, j: int) -> tuple:
        return tuple(Fraction(int(x == j)) for x in self.idx)

    def diff(self, a: int, b: int) -> tuple:
        """The undivided difference of w on {a..b}: sum_j (-1)^(b-j) C(b-a, j-a) w_j."""
        return tuple(Fraction((-1) ** (b - j) * comb(b - a, j - a)) if a <= j <= b else Fraction(0)
                     for j in self.idx)

    def interp(self, a: int, b: int, x: Fraction) -> tuple:
        """The Lagrange interpolant of w on {a..b}, evaluated at x."""
        out = []
        for j in self.idx:
            if not a <= j <= b:
                out.append(Fraction(0))
                continue
            c = Fraction(1)
            for m in range(a, b + 1):
                if m != j:
                    c *= (x - m) / Fraction(j - m)
            out.append(c)
        return tuple(out)


def _lin(*terms) -> tuple:
    """sum of c * form."""
    n = len(terms[0][1])
    return tuple(sum((c * f[i] for c, f in terms), Fraction(0)) for i in range(n))


def _dot(f: tuple, w) -> Fraction:
    return sum((a * b for a, b in zip(f, w)), Fraction(0))


# ---------------------------------------------------------------- branches

def _paths(g: Grid, cell: int, sel, tie: str):
    """(stencil (a, b), constraints) for every branch of the cell's selection; a constraint is (form, strict),
    meaning form . w >= 0 (or > 0)."""
    if isinstance(sel, dict):
        r = sel["fixed"]
        yield (cell - r, cell - r + g.k - 1), []
        return

    def rec(a, b, cons):
        if b - a + 1 == g.k:
            yield (a, b), cons
            return
        A, B = g.diff(a - 1, b), g.diff(a, b + 1)
        bma, bpa = _lin((1, B), (-1, A)), _lin((1, B), (1, A))
        left_strict = tie == "right"  # left on |A| < |B| (ties right) or |A| <= |B| (ties left)
        for s in (1, -1):  # |A| (<|<=) |B|: B - A and B + A both of sign s
            yield from rec(a - 1, b, cons + [(_lin((s, bma)), left_strict), (_lin((s, bpa)), left_strict)])
        for s in (1, -1):  # the complement: |B| (<=|<) |A|, i.e. A - B and A + B both of sign s
            yield from rec(a, b + 1, cons + [(_lin((-s, bma)), not left_strict), (_lin((s, bpa)), not left_strict)])

    yield from rec(cell, cell, [])


def branches(g: Grid, sel, tie: str):
    """(stencil of cell 0, stencil of cell 1, J, D, constraints) for every pair of branches."""
    half = Fraction(1, 2)
    for (s0, c0), (s1, c1) in product(list(_paths(g, 0, sel, tie)), list(_paths(g, 1, sel, tie))):
        J = _lin((1, g.interp(*s1, half)), (-1, g.interp(*s0, half)))
        D = _lin((1, g.unit(1)), (-1, g.unit(0)))
        yield s0, s1, J, D, c0 + c1


# ---------------------------------------------------------------- Fourier–Motzkin
# A constraint is (a, b, strict): a . x >= b, or > b. Variables are positions in a.

def _norm(c):
    a, b, s = c
    piv = next((abs(x) for x in a if x), None)
    if piv is None:
        return c
    return tuple(x / piv for x in a), b / piv, s


def _dedup(cons: list) -> list:
    best: dict = {}
    for c in map(_norm, cons):
        key = (c[0], c[1])
        best[key] = best.get(key, False) or c[2]
    return [(a, b, s) for (a, b), s in best.items()]


def fm_solve(cons: list, n: int):
    """A rational solution x of the system, or None if it has none (exact)."""
    levels = []
    cur = _dedup(cons)
    for v in range(n):
        levels.append(cur)
        P = [c for c in cur if c[0][v] > 0]
        N = [c for c in cur if c[0][v] < 0]
        new = [c for c in cur if c[0][v] == 0]
        for ap, bp, sp in P:
            for an, bn, sn in N:
                fp, fn = 1 / ap[v], -1 / an[v]
                new.append((tuple(fp * x + fn * y for x, y in zip(ap, an)), fp * bp + fn * bn, sp or sn))
        cur = _dedup(new)
        for a, b, s in cur:
            if not any(a) and (b > 0 or (s and b == 0)):
                return None
    for a, b, s in cur:
        if b > 0 or (s and b == 0):
            return None
    x = [Fraction(0)] * n
    for v in reversed(range(n)):
        lo = hi = None
        lo_s = hi_s = False
        for a, b, s in levels[v]:
            if a[v] == 0:
                continue
            rest = sum((a[j] * x[j] for j in range(v + 1, n)), Fraction(0))
            bound = (b - rest) / a[v]
            if a[v] > 0:  # x_v >= bound
                if lo is None or bound > lo:
                    lo, lo_s = bound, s
                elif bound == lo:
                    lo_s = lo_s or s
            elif hi is None or bound < hi:  # x_v <= bound
                hi, hi_s = bound, s
            elif bound == hi:
                hi_s = hi_s or s
        if lo is None and hi is None:
            x[v] = Fraction(0)
        elif hi is None:
            x[v] = lo + 1 if lo_s else lo
        elif lo is None:
            x[v] = hi - 1 if hi_s else hi
        else:
            x[v] = lo if lo == hi else (lo + hi) / 2
    return x


def fm_max(cons: list, obj: tuple, n: int):
    """sup obj . x over the closed system (strictness ignored), or None if unbounded; the system is assumed
    feasible. Adds t = obj . x as a last variable and eliminates the others."""
    ext = [(tuple(a) + (Fraction(0),), b, False) for a, b, _ in cons]
    row = tuple(obj) + (Fraction(-1),)
    ext += [(row, Fraction(0), False), (tuple(-x for x in row), Fraction(0), False)]
    cur = _dedup(ext)
    for v in range(n):
        P = [c for c in cur if c[0][v] > 0]
        N = [c for c in cur if c[0][v] < 0]
        new = [c for c in cur if c[0][v] == 0]
        for ap, bp, _ in P:
            for an, bn, _ in N:
                fp, fn = 1 / ap[v], -1 / an[v]
                new.append((tuple(fp * x + fn * y for x, y in zip(ap, an)), fp * bp + fn * bn, False))
        cur = _dedup(new)
    ups = [b / a[n] for a, b, _ in cur if a[n] < 0]  # a t >= b with a < 0: t <= b / a
    return min(ups) if ups else None


# ---------------------------------------------------------------- direct evaluation

def eno_values(w: dict, k: int, sel, tie: str) -> tuple[Fraction, Fraction]:
    """(w^+_0, w^-_1) by plain comparisons on the data w (dict j -> value): the independent check of a witness."""
    def stencil(cell):
        if isinstance(sel, dict):
            return cell - sel["fixed"], cell - sel["fixed"] + k - 1
        a = b = cell
        while b - a + 1 < k:
            A = sum((-1) ** (b - j) * comb(b - a + 1, j - a + 1) * w[j] for j in range(a - 1, b + 1))
            B = sum((-1) ** (b + 1 - j) * comb(b - a + 1, j - a) * w[j] for j in range(a, b + 2))
            if abs(A) < abs(B) or (abs(A) == abs(B) and tie == "left"):
                a -= 1
            else:
                b += 1
        return a, b

    def value(a, b):
        x, total = Fraction(1, 2), Fraction(0)
        for j in range(a, b + 1):
            c = Fraction(1)
            for m in range(a, b + 1):
                if m != j:
                    c *= (x - m) / Fraction(j - m)
            total += c * w[j]
        return total

    return value(*stencil(0)), value(*stencil(1))


# ---------------------------------------------------------------- the decision

def _failing(claim: dict, J: tuple, D: tuple) -> list[tuple[str, list]]:
    """The systems (label, constraints as (form, strict) on w) whose solutions break the claim."""
    neg = lambda f: tuple(-x for x in f)
    if claim["claim"] == "eno_sign_property":
        return [("D > 0, J < 0", [(D, True), (neg(J), True)]), ("D < 0, J > 0", [(neg(D), True), (J, True)]),
                ("D = 0, J > 0", [(D, False), (neg(D), False), (J, True)]),
                ("D = 0, J < 0", [(D, False), (neg(D), False), (neg(J), True)])]
    c = Fraction(str(claim["c"]))
    E = _lin((1, J), (-c, D))
    return [(f"D > 0, J > {c} D", [(D, True), (E, True)]), (f"D < 0, J < {c} D", [(neg(D), True), (neg(E), True)])]


def _reduce(cons: list, g: Grid) -> tuple[list, int]:
    """Drop w_0 (fixed at 0 by translation invariance): (a, b, strict) on the other variables."""
    drop = g.idx.index(0)
    return [(tuple(x for i, x in enumerate(f) if i != drop), Fraction(0), s) for f, s in cons], g.n - 1


def _lift(x: list, g: Grid) -> dict:
    drop = g.idx.index(0)
    vals = list(x[:drop]) + [Fraction(0)] + list(x[drop:])
    return dict(zip(g.idx, vals))


def parse_spec(rec: dict) -> tuple[int, object, str]:
    k = rec["order"]
    if not isinstance(k, int) or k < 1:
        raise ValueError("order must be a positive integer")
    sel = rec["selection"]
    tie = rec.get("tie", "left")
    if sel == "eno":
        if tie not in ("left", "right"):
            raise ValueError("tie must be 'left' or 'right'")
    elif isinstance(sel, dict) and set(sel) == {"fixed"} and isinstance(sel["fixed"], int):
        if not 0 <= sel["fixed"] <= k - 1:
            raise ValueError("a fixed stencil {i - r .. i - r + k - 1} needs 0 <= r <= k - 1")
    else:
        raise ValueError("selection is 'eno' or {'fixed': r}")
    return k, sel, tie


def decide(k: int, sel, tie: str, claim: dict) -> dict:
    g = Grid(k)
    n_branch = n_sys = 0
    ratio = claim["claim"] == "eno_jump_ratio_at_most"
    for s0, s1, J, D, cons in branches(g, sel, tie):
        base, nv = _reduce(cons, g)
        if fm_solve(base, nv) is None:
            continue  # an empty branch
        n_branch += 1
        for label, extra in _failing(claim, J, D):
            n_sys += 1
            sysc, _ = _reduce(cons + extra, g)
            x = fm_solve(sysc, nv)
            if x is None:
                continue
            w = _lift(x, g)
            wp, wm = eno_values(w, k, sel, tie)
            Jv, Dv = wm - wp, w[1] - w[0]
            bad = (Jv * Dv < 0 or (Dv == 0 and Jv != 0)) if not ratio else (Dv != 0 and Jv / Dv > Fraction(str(claim["c"])))
            if not bad:
                raise AssertionError(f"the branch solution {w} does not break the claim on direct evaluation")
            return {"verdict": REFUTED, "data": {f"w_{j}": str(v) for j, v in w.items()}, "jump": str(Jv),
                    "difference": str(Dv), "stencils": {"cell i": list(s0), "cell i+1": list(s1)},
                    "reason": f"for these data ({label}) the jump is {Jv} and w_(i+1) - w_i = {Dv} (stencils "
                              f"{list(s0)}, {list(s1)} relative to i, checked by direct evaluation)"}
    out = {"verdict": VERIFIED, "branches": n_branch, "systems": n_sys,
           "reason": f"each of the {n_sys} failing systems over the {n_branch} non-empty selection branches is "
                     "infeasible (Fourier–Motzkin, exact, strictness tracked)"}
    return out


def sup_ratio(k: int, sel, tie: str) -> str:
    """sup J / D over all data with D != 0 (by symmetry w -> -w, over D = 1): the largest maximum of J on the
    closure of a branch with D = 1, over the branches where D = 1 is feasible; "unbounded" if one is unbounded."""
    g = Grid(k)
    drop = g.idx.index(0)
    red = lambda f: tuple(x for i, x in enumerate(f) if i != drop)
    sup = None
    for _, _, J, D, cons in branches(g, sel, tie):
        base, nv = _reduce(cons, g)
        one = base + [(red(D), Fraction(1), False), (tuple(-x for x in red(D)), Fraction(-1), False)]
        if fm_solve(one, nv) is None:
            continue
        m = fm_max(one, red(J), nv)
        if m is None:
            return "unbounded"
        sup = m if sup is None else max(sup, m)
    return str(sup)


def check_claim(rec: dict, claim: dict) -> dict:
    try:
        k, sel, tie = parse_spec(rec)
        if claim["claim"] == "eno_jump_ratio_at_most":
            Fraction(str(claim["c"]))
    except (KeyError, ValueError, TypeError) as e:
        return {"verdict": UNKNOWN, "reason": f"bad spec: {e}"}
    if k > MAX_ORDER:
        return {"verdict": UNKNOWN, "reason": f"order {k} > {MAX_ORDER}: the branch enumeration is not attempted"}
    out = decide(k, sel, tie, claim)
    if claim["claim"] == "eno_jump_ratio_at_most":
        out["sup_ratio"] = sup_ratio(k, sel, tie)  # for the record; the verdict does not use it
    return out


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
    print("| spec | claim | expected | verdict | detail |\n|---|---|---|---|---|")
    wrong = unsure = 0
    for path in paths:
        spec = json.loads(path.read_text())
        for c, r in zip(spec["claims"], check(spec)["claims"]):
            ok = r["verdict"] == c.get("expect")
            flag = "" if ok else ("  (UNSURE, differs)" if c.get("confidence") == "unsure" else "  (WRONG)")
            wrong += not ok and c.get("confidence") != "unsure"
            unsure += not ok and c.get("confidence") == "unsure"
            name = c["claim"] + (f" c = {c['c']}" if "c" in c else "")
            detail = (f"sup J/D = {r['sup_ratio']}; " if "sup_ratio" in r else "") + (
                f"data {r['data']}" if "data" in r else f"{r.get('branches', '')} branches")
            print(f"| {path.stem} | {name} | {c.get('expect')} | {r['verdict']}{flag} | {detail} |")
    print(f"\n{wrong} not as expected, {unsure} unsure expectations differ")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
