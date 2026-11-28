"""A small exact linear-programming solver over Fractions: two-phase simplex with Bland's rule.

Used by `ssp_class.py` to decide whether a list of linear (in)equalities implies another one. Every
answer it gives there is re-checked independently of the solver: a Farkas certificate (multipliers
y with A^T y = t, y >= 0 on the inequality rows, and b.y + t0 >= 0) is replayed as an identity, and a
counterexample point is substituted into every condition. So a solver bug can only cost an answer
(UNKNOWN), never give a wrong VERIFIED or REFUTED.

Bland's rule (smallest index enters, smallest basic index leaves on ties) cannot cycle, so the
simplex terminates; the problems here have a few dozen variables.
"""

from __future__ import annotations

from fractions import Fraction

ZERO = Fraction(0)


def _pivot(T: list, basis: list, row: int, col: int) -> None:
    piv = T[row][col]
    T[row] = [x / piv for x in T[row]]
    for i in range(len(T)):
        if i != row and T[i][col]:
            f = T[i][col]
            T[i] = [a - f * b for a, b in zip(T[i], T[row])]
    basis[row] = col


def _simplex(T: list, basis: list, cost: list, cols: list) -> tuple[str, int | None]:
    """Minimise cost.z on the tableau T (rows [M | r]) from the feasible basis; only `cols` may enter.
    ('optimal', None) or ('unbounded', the entering column with no leaving row)."""
    while True:
        enter = None
        for j in cols:
            if j in basis:
                continue
            rc = cost[j] - sum((cost[b] * T[i][j] for i, b in enumerate(basis)), ZERO)
            if rc < 0:
                enter = j
                break
        if enter is None:
            return "optimal", None
        best = None
        for i in range(len(T)):
            if T[i][enter] > 0:
                key = (T[i][-1] / T[i][enter], basis[i])
                if best is None or key < best[0]:
                    best = (key, i)
        if best is None:
            return "unbounded", enter
        _pivot(T, basis, best[1], enter)


def minimize(c: list, M: list, r: list) -> dict:
    """min c.z subject to M z = r, z >= 0 (Fractions). Returns {"status": "optimal", "z", "value"},
    {"status": "unbounded", "z" (feasible), "ray" (d >= 0, M d = 0, c.d < 0)} or {"status": "infeasible"}."""
    n = len(c)
    rows = [list(row) + [rhs] for row, rhs in zip(M, r)]
    rows = [[-x for x in row] if row[-1] < 0 else row for row in rows]
    m = len(rows)
    # phase 1: artificial columns n .. n+m-1
    T = [row[:-1] + [Fraction(int(i == k)) for k in range(m)] + [row[-1]] for i, row in enumerate(rows)]
    basis = list(range(n, n + m))
    cost1 = [ZERO] * n + [Fraction(1)] * m
    _simplex(T, basis, cost1, list(range(n + m)))
    if sum((T[i][-1] for i, b in enumerate(basis) if b >= n), ZERO) > 0:
        return {"status": "infeasible"}
    # drive artificials out of the basis; a row with no non-zero original column is redundant
    keep = []
    for i in range(m):
        if basis[i] >= n:
            j = next((j for j in range(n) if T[i][j]), None)
            if j is None:
                continue
            _pivot(T, basis, i, j)
        keep.append(i)
    T = [T[i][:n] + [T[i][-1]] for i in keep]
    basis = [basis[i] for i in keep]
    status, enter = _simplex(T, basis, list(c), list(range(n)))
    z = [ZERO] * n
    for i, b in enumerate(basis):
        z[b] = T[i][-1]
    if status == "unbounded":
        d = [ZERO] * n
        d[enter] = Fraction(1)
        for i, b in enumerate(basis):
            d[b] = -T[i][enter]
        return {"status": "unbounded", "z": z, "ray": d}
    return {"status": "optimal", "z": z, "value": sum((ci * zi for ci, zi in zip(c, z)), ZERO)}


# ---------------------------------------------------------------- linear systems over named variables

def _dot(a: dict, x: dict) -> Fraction:
    return sum((v * x.get(k, ZERO) for k, v in a.items()), ZERO)


def holds(cond: tuple, x: dict) -> bool:
    """cond = (const, {var: coef}, rel) means const + sum coef*var rel 0, rel in '>=', '>', '='."""
    c0, lin, rel = cond
    v = c0 + _dot(lin, x)
    return v >= 0 if rel == ">=" else v > 0 if rel == ">" else v == 0


def minimize_affine(conds: list, target: tuple, names: list) -> dict:
    """min of the affine target (t0, {var: t}) over {x : every cond holds, strict ones relaxed to >=}.
    {"status": "infeasible"}, {"status": "unbounded", "point", "ray"} or {"status": "optimal", "point", "value"};
    points are dicts over `names`. Free variables are split x = p - q."""
    n = len(names)
    ineq = [c for c in conds if c[2] != "="]
    eq = [c for c in conds if c[2] == "="]
    ncol = 2 * n + len(ineq)
    M, r = [], []
    for k, (c0, lin, _) in enumerate(ineq):           # c0 + a.x - s = 0, s >= 0
        row = [lin.get(v, ZERO) for v in names] + [-lin.get(v, ZERO) for v in names] + [ZERO] * len(ineq)
        row[2 * n + k] = Fraction(-1)
        M.append(row)
        r.append(-c0)
    for c0, lin, _ in eq:
        M.append([lin.get(v, ZERO) for v in names] + [-lin.get(v, ZERO) for v in names] + [ZERO] * len(ineq))
        r.append(-c0)
    t0, t = target
    cost = [t.get(v, ZERO) for v in names] + [-t.get(v, ZERO) for v in names] + [ZERO] * len(ineq)
    if not M:
        M, r = [[ZERO] * ncol], [ZERO]
    out = minimize(cost, M, r)
    point = lambda z: {v: z[i] - z[n + i] for i, v in enumerate(names)}
    if out["status"] == "infeasible":
        return out
    if out["status"] == "unbounded":
        return {"status": "unbounded", "point": point(out["z"]), "ray": point(out["ray"])}
    return {"status": "optimal", "point": point(out["z"]), "value": t0 + out["value"]}


def farkas(conds: list, target: tuple, names: list) -> dict | None:
    """Multipliers y for `target >= 0` from the relaxed conditions: target = r + sum_j y_j cond_j with
    y_j >= 0 on inequality rows, y_j free on equalities, r >= 0 a constant. Solved as an LP (max r),
    then replayed exactly. None if no such certificate exists."""
    t0, t = target
    m = len(conds)
    # variables: y_ineq >= 0, y_eq = p - q; constraints: sum_j y_j a_j = t (each name)
    cols = []
    for j, (c0, lin, rel) in enumerate(conds):
        cols.append((j, 1))
        if rel == "=":
            cols.append((j, -1))
    M = [[s * conds[j][1].get(v, ZERO) for j, s in cols] for v in names]
    r = [t.get(v, ZERO) for v in names]
    # maximise r = t0 - sum_j y_j c0_j, i.e. minimise sum_j y_j c0_j
    cost = [s * conds[j][0] for j, s in cols]
    if not M:
        M, r = [[ZERO] * len(cols)], [ZERO]
    if not cols:
        return {"multipliers": [], "remainder": t0} if not any(t.values()) and t0 >= 0 else None
    out = minimize(cost, M, r)
    if out["status"] != "optimal":
        return None
    y = [ZERO] * m
    for (j, s), z in zip(cols, out["z"]):
        y[j] += s * z
    return replay(conds, target, names, y)


def replay(conds: list, target: tuple, names: list, y: list) -> dict | None:
    """Check target - sum_j y_j cond_j = r with r a constant >= 0 and y_j >= 0 on inequalities, exactly."""
    t0, t = target
    if any(yj < 0 for yj, c in zip(y, conds) if c[2] != "="):
        return None
    for v in set(names) | set(t) | {k for c in conds for k in c[1]}:
        if t.get(v, ZERO) != sum((yj * c[1].get(v, ZERO) for yj, c in zip(y, conds)), ZERO):
            return None
    rem = t0 - sum((yj * c[0] for yj, c in zip(y, conds)), ZERO)
    if rem < 0:
        return None
    return {"multipliers": y, "remainder": rem}
