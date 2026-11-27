"""Exact checks for limited (piecewise-polynomial) schemes on stencils up to five points wide.

A limited update H(u_{i-2}, ..., u_{i+2}, lam) is built from polynomials and |x| = sqrt(x^2) (min,
max and minmod are written that way, see `expr.piecewise`). Splitting every |x| into the closed
cases x >= 0 and x <= 0 gives sign cells on which H is a polynomial (`cells`). For the Sweby
flux-limited schemes of linear advection the cell atoms are linear forms in the u's and H is linear
in the u's on each cell, so each cell is a linear scheme: the checks below are exact per cell.

Exhaustiveness. A verdict that quantifies over all states rests on the cells covering the whole
state space. Here the cover holds by construction: each split replaces a cell K by K & {x >= 0} and
K & {x <= 0}, which cover K. A cell is dropped only with a Farkas certificate that it lies in a
hyperplane (some atom a has -a >= 0 on it, so a = 0 there). The retained closed cells still cover
everything: their union R is closed, and its complement is open and lies inside the finitely many
hyperplanes of the dropped cells, so it is empty. `cells` caps the number of cells explored
(MAX_CELLS) and raises Undecided past it, so a check gives UNKNOWN rather than a verdict on the
branches it happened to enumerate. Where two retained cells overlap (the atoms on which they take
opposite signs vanish), their polynomials must agree; `cells` asserts it on the linear subspace
those atoms cut out (cheap, and it would catch a bug in the splitting).

Checks:
- `tvd_harten` (SUFFICIENT for TVD): Harten's lemma with the upwind decomposition, certified per
  cell by Farkas identities whose multipliers are polynomials in nu, non-negative on the CFL range.
- `tv_increase` (NECESSARY for TVD): an explicit periodic rational data vector whose total variation
  grows in one step at a rational nu in the claimed range, in Fraction arithmetic.
- `truncation_branches` (SUFFICIENT for the pointwise truncation order on smooth data): the exact
  truncation order of the linear scheme on every cell (the per-branch table).
- `truncation_smooth_data` (NECESSARY for it): an explicit smooth (polynomial) exact solution and
  grid placement whose stencil sits in a lower-order branch for every small dx, with the local
  truncation error computed exactly as a polynomial in dx.
"""

from __future__ import annotations

import random
from fractions import Fraction
from itertools import combinations
from math import lcm

from ..expr import intern, parse, substitute, to_str
from . import checks, linear, poly as P
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

MAX_CELLS = 4000          # cells explored (internal nodes of the split tree included) before giving up
MAX_DEPTH_NU = 5          # bisection depth of the nu-interval in the Farkas certificates
NU = P.var("nu")

COVER = ("cover by construction: every |x| is split into the closed cells x >= 0 and x <= 0, which cover "
         "their parent; a cell is dropped only with a Farkas certificate that it lies in a hyperplane, and "
         "the retained closed cells still cover the state space (their union is closed and its complement "
         "is an open subset of finitely many hyperplanes, hence empty)")


# ---------------------------------------------------------------- sign cells with pruning

class TooMany(P.Undecided):
    pass


def _hook(assign):
    """checks.sign_cells' sqrt hook: |x| from the assignment, or a request to split on x."""
    def h(node, rec):
        a = node.args[0]
        if a.kind != "powi" or a.q % 2:
            raise P.Undecided("square root of something other than an even power")
        x = P.power(rec(a.args[0]), a.q // 2)
        if set(x) <= {()}:
            return P.const(abs(x.get((), Fraction(0))))
        g = abs(min(x.items(), key=lambda mc: P._key(mc[0]))[1])     # |x| = g*|x/g|: 2x and x share one atom
        x = P.scale(x, 1 / g)
        for key, sgn in ((checks._key(x), 1), (checks._key(P.scale(x, -1)), -1)):
            if key in assign:
                return P.scale(x, g * sgn * assign[key][1])
        raise checks._Split(x)
    return h


def normal(e, assign: dict, memo: dict | None = None) -> P.Poly:
    """P.from_expr(e, _hook(assign)) for the polynomial fragment, memoized over shared subtrees (pass an
    `intern`ed e): the same normal form, computed once per distinct subexpression."""
    memo = {} if memo is None else memo
    if id(e) in memo:
        return memo[id(e)][1]
    k, a = e.kind, e.args
    rec = lambda x: normal(x, assign, memo)
    if k == "var": out = P.var(e.name)
    elif k == "lit": out = P.const(e.q)
    elif k == "neg": out = P.scale(rec(a[0]), -1)
    elif k == "add": out = P.add(rec(a[0]), rec(a[1]))
    elif k == "sub": out = P.add(rec(a[0]), rec(a[1]), -1)
    elif k == "mul": out = P.mul(rec(a[0]), rec(a[1]))
    elif k == "div": out = P.mul(rec(a[0]), P.inverse(rec(a[1])))
    elif k == "powi": out = P.power(rec(a[0]), e.q)
    elif k == "sqrt": out = _hook(assign)(e, rec)
    else: raise P.Undecided(f"{k} is outside the polynomial fragment")
    memo[id(e)] = (e, out)
    return out


def on_cell(e, assign) -> P.Poly | None:
    """The polynomial of expression e on the cell given by `assign`, or None if e needs a sign the
    cell does not fix."""
    try:
        return P.from_expr(e, _hook(assign))
    except checks._Split:
        return None


def _atoms(assign: dict, extra=()) -> list:
    return [P.scale(x, s) for x, s in assign.values()] + list(extra)


def _interior(atoms: list, names: list, tries: int = 64) -> dict | None:
    """A small integer point where every atom is > 0 (so the cell is full-dimensional), or None."""
    rng = random.Random(len(atoms))
    for _ in range(tries):
        pt = {x: Fraction(rng.randint(-6, 6)) for x in names}
        if all((v := P.evaluate(a, pt)) is not None and v > 0 for a in atoms):
            return pt
    return None


def feasible(cols: list, b: list) -> list | None:
    """A basic solution mu >= 0 of sum_j mu_j cols[j] = b (vectors as lists), exactly, or None if there is
    none: phase 1 of the simplex method with Bland's rule, in Fraction arithmetic. Only a search: every
    caller re-checks the identity it builds from mu."""
    m, n = len(b), len(cols)
    sign = [1 if x >= 0 else -1 for x in b]
    T = [[sign[i] * Fraction(cols[j][i]) for j in range(n)] + [Fraction(int(i == k)) for k in range(m)]
         + [sign[i] * Fraction(b[i])] for i in range(m)]
    basis = list(range(n, n + m))
    while True:
        # reduced costs of the phase-1 objective (the sum of the artificial variables)
        red = [Fraction(int(j >= n)) - sum(T[i][j] for i in range(m) if basis[i] >= n) for j in range(n + m)]
        enter = next((j for j in range(n + m) if red[j] < 0 and j not in basis), None)
        if enter is None:
            break
        rows = [(T[i][-1] / T[i][enter], basis[i], i) for i in range(m) if T[i][enter] > 0]
        if not rows:
            break
        _, _, r = min(rows)
        piv = T[r][enter]
        T[r] = [x / piv for x in T[r]]
        for i in range(m):
            if i != r and T[i][enter]:
                f = T[i][enter]
                T[i] = [x - f * y for x, y in zip(T[i], T[r])]
        basis[r] = enter
    if any(basis[i] >= n and T[i][-1] != 0 for i in range(m)):
        return None
    mu = [Fraction(0)] * n
    for i, bj in enumerate(basis):
        if bj < n:
            mu[bj] = T[i][-1]
    return mu


def _lin_vectors(atoms: list, names: list) -> list | None:
    lins = [checks._linear(a, names) for a in atoms]
    if any(l is None or l[0] for l in lins):                  # homogeneous linear atoms only
        return None
    return [[l[1].get(x, Fraction(0)) for x in names] for l in lins]


def lower_dimensional(atoms: list) -> dict | None:
    """A certificate that the closed cell {a >= 0 for a in atoms} lies in a hyperplane: an atom a with
    -a >= 0 on the cell (a Farkas identity with non-negative multipliers), so a = 0 on it. None if the
    cell has an interior point or no certificate is found (the cell is then kept, which is always
    safe). By Gordan's alternative a homogeneous cell with no interior point has such an atom, and the
    exact simplex search finds it."""
    names = sorted(set().union(*(P.variables(a) for a in atoms))) if atoms else []
    if not atoms or _interior(atoms, names):
        return None
    vecs = _lin_vectors(atoms, names)
    if vecs is None:
        return None
    mu = feasible([v + [Fraction(1)] for v in vecs], [Fraction(0)] * len(names) + [Fraction(1)])
    if mu is None:
        return None
    j = next(j for j, m in enumerate(mu) if m)
    rest = P.scale(atoms[j], -1)                              # -a_j = sum_{i != j} (mu_i/mu_j) a_i
    terms = [(m / mu[j], a) for i, (m, a) in enumerate(zip(mu, atoms)) if m and i != j]
    for m, a in terms:
        rest = P.add(rest, P.scale(a, m), -1)
    if rest:
        return None
    return {"atom": P.show(atoms[j]), "is <= 0 on the cell": f"-({P.show(atoms[j])}) = " + (
        " + ".join(f"{m}*({P.show(a)})" for m, a in terms) or "0")}


def lsubst(p: P.Poly, sub: dict) -> P.Poly:
    """P.subst for a substitution of linear forms into a polynomial linear in the substituted variables
    (the cell polynomials and atoms here); falls back to P.subst otherwise."""
    out: P.Poly = {}
    for m, c in p.items():
        hits = [(x, k) for x, k in m if x[0] == "v" and x[1] in sub]
        if not hits:
            out = P.add(out, {m: c})
            continue
        if len(hits) > 1 or hits[0][1] != 1 or any(x[0] == "s" for x, _ in m):
            return P.subst(p, sub)
        rest = dict(x for x in m if x != hits[0])
        for m2, c2 in sub[hits[0][0][1]].items():
            d = dict(rest)
            for x, k in m2:
                d[x] = d.get(x, 0) + k
            out = P.add(out, {P._mono(d): c * c2})
    return out


def _solve_hyperplanes(eqs: list) -> dict | None:
    """{variable: Poly} expressing some variables through the others on {e = 0 for e in eqs} (linear e)."""
    sub: dict = {}
    for e in eqs:
        e = lsubst(e, sub)
        if not e:
            continue
        names = sorted(P.variables(e))
        lin = checks._linear(e, names)
        if lin is None:
            return None
        c0, cs = lin
        if not cs:
            return None                                     # a non-zero constant: the subspace is empty
        x = next(iter(sorted(cs)))
        val = P.scale(P.add(e, P.scale(P.var(x), cs[x]), -1), Fraction(-1) / cs[x])
        sub = {k: lsubst(v, {x: val}) for k, v in sub.items()}
        sub[x] = val
    return sub


def _agree(c1: dict, c2: dict) -> bool | None:
    """Do the two cells' polynomials agree on the overlap K1 & K2? First on the subspace where the atoms
    of opposite sign vanish (which contains the overlap); if they differ there, on the linear span of
    the overlap, cut out by its implicit equalities (atoms a with -a >= 0 on K1 & K2, found exactly).
    A polynomial that vanishes on a cone vanishes on its span, so the second test is exact. None if
    undecided."""
    diff = P.add(c1["poly"], c2["poly"], -1)
    opp = [x for k, (x, s) in c1["assign"].items() if k in c2["assign"] and c2["assign"][k][1] != s]
    sub = _solve_hyperplanes(opp)
    if sub is not None and not lsubst(diff, sub):
        return True
    sub = span(c1["atoms"] + c2["atoms"], opp)
    return None if sub is None else not lsubst(diff, sub)


def span(atoms: list, eqs: list) -> dict | None:
    """The linear span of the cone {a >= 0 for a in atoms}, known to lie in {e = 0 for e in eqs}, as a
    substitution (`_solve_hyperplanes`). Gordan's alternative, repeated: in the current subspace either
    some mu >= 0, sum mu = 1, has sum_j mu_j a_j = 0 (then every a_j with mu_j > 0 vanishes on the cone;
    add them and repeat), or a point makes every remaining atom > 0, so the subspace is the span."""
    eqs = list(eqs)
    while True:
        sub = _solve_hyperplanes(eqs)
        if sub is None:
            return None
        cur = [b for a in atoms if (b := lsubst(a, sub))]
        names = sorted(set().union(*(P.variables(b) for b in cur))) if cur else []
        vecs = _lin_vectors(cur, names) if cur else []
        if vecs is None:
            return None
        if not cur:
            return sub
        mu = feasible([v + [Fraction(1)] for v in vecs], [Fraction(0)] * len(names) + [Fraction(1)])
        if mu is None:
            return sub
        total: P.Poly = {}
        for m, b in zip(mu, cur):
            total = P.add(total, P.scale(b, m))
        if total:                                           # re-check the identity the search found
            return None
        eqs += [b for m, b in zip(mu, cur) if m]


_CACHE: dict = {}


def cells(e, extra=(), cap: int | None = None) -> dict:
    """`_cells`, cached per expression (the TVD and truncation checks share one decomposition)."""
    cap = MAX_CELLS if cap is None else cap
    key = (to_str(e), tuple(checks._key(a) for a in extra), cap)
    if key not in _CACHE:
        _CACHE[key] = _cells(e, extra, cap)
    return _CACHE[key]


def _cells(e, extra=(), cap: int = MAX_CELLS) -> dict:
    """Sign cells of e with lower-dimensional cells pruned (see the module docstring for why the
    retained ones still cover the space). `extra` atoms are added to every cell (for example a CFL
    atom or the sign of one difference). Returns {"cells": [{"poly", "atoms", "assign"}], "explored",
    "pruned": [certificates], "overlaps_checked", "cover"}; raises TooMany past `cap` explored cells
    and Undecided if two overlapping cells disagree."""
    todo, out, pruned, explored = [{}], [], [], 0
    e = intern(e)
    while todo:
        assign = todo.pop()
        explored += 1
        if explored > cap:
            raise TooMany(f"more than {cap} sign cells explored; giving up (UNKNOWN, not a verdict)")
        try:
            p = normal(e, assign)
        except checks._Split as s:
            for sgn in (1, -1):
                a2 = {**assign, checks._key(s.p): (s.p, sgn)}
                cert = lower_dimensional(_atoms(a2, extra))
                if cert:
                    pruned.append(cert)
                else:
                    todo.append(a2)
            continue
        out.append({"poly": p, "atoms": _atoms(assign, extra), "assign": assign})
    checked = undecided = 0
    for c1, c2 in combinations(out, 2):
        ok = _agree(c1, c2)
        if ok is False:
            raise P.Undecided(f"cells {[_show(a) for a in c1['atoms']]} and {[_show(a) for a in c2['atoms']]} "
                              "disagree where they overlap: a bug in the sign-cell split")
        checked += ok is True
        undecided += ok is None
    return {"cells": out, "explored": explored, "pruned": pruned, "overlaps_checked": checked,
            "overlaps_undecided": undecided, "cover": COVER}


def _show(a: P.Poly) -> str:
    return f"{P.show(a)} >= 0"


def cell_counts(cs: dict) -> dict:
    return {"retained (full-dimensional)": len(cs["cells"]), "pruned (lower-dimensional, certified)": len(cs["pruned"]),
            "explored (split-tree nodes)": cs["explored"], "pairs checked to agree on their overlap": cs["overlaps_checked"],
            "pairs whose overlap check was undecided": cs["overlaps_undecided"]}


# ---------------------------------------------------------------- linear flux, nu = a*lam

def _advection(spec: dict) -> Fraction:
    """a for f = a*u, else NotLinear."""
    f = P.from_expr(checks.pde_flux(spec))
    if list(f) != [((("v", "u"), 1),)]:
        raise checks.NonlinearFlux(f"nonlinear flux f = {P.show(f)}")
    return f[((("v", "u"), 1),)]


def _in_nu(p: P.Poly, a: Fraction) -> P.Poly:
    return P.subst(p, {"lam": P.scale(NU, 1 / a)})


def _nu_parts(p: P.Poly) -> dict | None:
    """{k: Poly free of nu} with p = sum_k nu^k p_k, or None for a negative power of nu."""
    out: dict = {}
    for m, c in p.items():
        d = dict(m)
        k = d.pop(("v", "nu"), 0)
        if k < 0:
            return None
        out[k] = P.add(out.get(k, {}), {P._mono(d): c})
    return out


def _coeffs(parts: dict) -> list:
    c = [Fraction(0)] * (max(parts, default=0) + 1)
    for k, v in parts.items():
        c[k] = v
    return c


def _poly_nu(c: list) -> P.Poly:
    out: P.Poly = {}
    for k, v in enumerate(c):
        out = P.add(out, P.scale(P.power(NU, k), v))
    return out


def farkas_in_nu(p: P.Poly, atoms: list, lo: Fraction, hi: Fraction) -> dict | None:
    """A certificate that p >= 0 on {a >= 0 for a in atoms} for every nu in [lo, hi]: p is linear in the
    state variables with coefficients polynomial in nu, the atoms are linear and free of nu. On each
    piece of a bisection of [lo, hi], p = sum_j mu_j(nu) a_j as an identity of polynomials, with every
    mu_j having non-negative Bernstein coefficients on the piece. For fixed nu this is Farkas' lemma for
    cones (`checks.certify_farkas` is the affine version). The atoms used on a piece come from an exact
    LP at a sample nu (the support of a basic solution, so they are independent and mu(nu) is unique);
    the identity is then solved for every power of nu and replayed in the normal form. If the LP is
    infeasible at some nu in [lo, hi], p < 0 somewhere on the cell there and no certificate exists."""
    parts = _nu_parts(p)
    if parts is None or any(P.variables(a) & {"nu", "lam"} for a in atoms):
        return None
    names = sorted(set().union(*(P.variables(q) for q in parts.values()), *(P.variables(a) for a in atoms)))
    vecs = _lin_vectors(atoms, names)
    lins = {k: _lin_vectors([q], names) for k, q in parts.items()}
    if vecs is None or any(v is None for v in lins.values()):
        return None
    lins = {k: v[0] for k, v in lins.items()}
    deg = max(parts, default=0)
    at = lambda nu: [sum((lins[k][i] * nu ** k for k in lins), Fraction(0)) for i in range(len(names))]

    def basis(nu):
        mu = feasible(vecs, at(nu))
        if mu is None:
            return "infeasible"
        js = [j for j, m in enumerate(mu) if m]
        mus = [[Fraction(0)] * (deg + 1) for _ in js]
        for k, lin in lins.items():
            sol = checks._solve([dict(zip(names, vecs[j])) for j in js], dict(zip(names, lin)), names)
            if sol is None:
                return None
            for row, v in zip(mus, sol):
                row[k] = v
        return js, mus

    every: list = []

    def all_bases():
        """Every independent subset of atoms with its unique mu(nu) (the fallback when the LP's basis
        at the sample points is degenerate)."""
        if not every:
            for size in range(1, len(names) + 1):
                for js in combinations(range(len(atoms)), size):
                    mus = [[Fraction(0)] * (deg + 1) for _ in js]
                    for k, lin in lins.items():
                        sol = checks._solve([dict(zip(names, vecs[j])) for j in js], dict(zip(names, lin)), names)
                        if sol is None:
                            break
                        for row, v in zip(mus, sol):
                            row[k] = v
                    else:
                        every.append((list(js), mus))
        return every

    pieces, todo = [], [(lo, hi, 0)]
    while todo:
        a0, b0, depth = todo.pop(0)
        found, cands = None, []
        for nu in dict.fromkeys(((a0 + b0) / 2, a0, b0)):
            got = basis(nu)
            if got == "infeasible":                            # p < 0 somewhere on the cell at this nu
                return None
            if got is not None:
                cands.append(got)
        for js, mus in cands:
            bs = [checks.bernstein(list(c), a0, b0) for c in mus]
            if all(min(b) >= 0 for b in bs):
                found = (js, mus, bs)
                break
        if not found:
            for js, mus in all_bases():
                bs = [checks.bernstein(list(c), a0, b0) for c in mus]
                if all(min(b) >= 0 for b in bs):
                    found = (js, mus, bs)
                    break
        if found:
            pieces.append((a0, b0, *found))
        elif depth >= MAX_DEPTH_NU or a0 == b0:
            return None
        else:
            m = (a0 + b0) / 2
            todo += [(a0, m, depth + 1), (m, b0, depth + 1)]
    out = []
    for a0, b0, js, mus, bs in sorted(pieces, key=lambda t: t[0]):
        rest = p                                                  # replay the identity in the normal form
        for c, j in zip(mus, js):
            rest = P.add(rest, P.mul(_poly_nu(c), atoms[j]), -1)
        if rest:
            return None
        out.append({"nu": [str(a0), str(b0)],
                    "identity": f"{P.show(p)} = " + (" + ".join(
                        f"({P.show(_poly_nu(c))})*({P.show(atoms[j])})" for c, j in zip(mus, js)) or "0"),
                    "bernstein_min": str(min((min(b) for b in bs), default=Fraction(0)))})
    return {"pieces": out}


# ---------------------------------------------------------------- TVD: Harten's lemma (sufficient)

HARTEN = ("Harten's lemma (1983): if u_i^{n+1} = u_i - C_{i-1/2} Delta_{i-1/2} + D_{i+1/2} Delta_{i+1/2} with "
          "C, D >= 0 and C_{i+1/2} + D_{i+1/2} <= 1 for every state, then TV(u^{n+1}) <= TV(u^n) "
          "(Delta_{i+1/2} = u_{i+1} - u_i)")


def _tvd_range(spec: dict):
    r = spec.get("claims", {}).get("tvd_cfl")
    return None if r is None else tuple(Fraction(x) for x in r)


def tvd_claim(r) -> str:
    return (f"TVD: sum_i |u_{{i+1}}^{{n+1}} - u_i^{{n+1}}| <= sum_i |u_{{i+1}}^n - u_i^n| for every periodic (or "
            f"compactly supported) state and every nu = a*dt/dx in [{r[0]}, {r[1]}]")


def tvd_harten(spec: dict) -> dict:
    """Harten's incremental form with the upwind split, certified exactly on every sign cell.

    For a > 0 take D = 0 and C_{i-1/2} = -N/Delta, where N = H - u_i and Delta = u_i - u_{i-1}
    (defined where Delta != 0; where Delta = 0 the certificate shows N = 0, so any C works). Each
    cell is split once more by the sign s of Delta, and on s*Delta >= 0 we certify, as polynomial
    identities in nu valid on the whole CFL range (`farkas_in_nu`):
        -s*N >= 0            (C >= 0, that is C*Delta^2 = -N*Delta >= 0)
        s*(N + Delta) >= 0   (C <= 1, that is (1 - C)*Delta^2 = Delta^2 + N*Delta >= 0).
    No division by Delta occurs. For a < 0 the mirror split (C = 0, D_{i+1/2} = N/(u_{i+1} - u_i))
    is used. Harten's form is not unique, so a failure here is not a refutation: UNKNOWN.

    TODO: general C, D >= 0 with C + D <= 1 (centred schemes need both; for linear schemes
    `linear.tvd_linear` decides TVD exactly instead). We plan a separate Lean statement of Harten's lemma."""
    r = _tvd_range(spec)
    if r is None:
        return result("tvd_harten", NOT_APPLICABLE, "TVD", "no CFL range claimed (claims.tvd_cfl)")
    lo, hi = r
    claim = tvd_claim(r)
    try:
        a = _advection(spec)
        e = checks.update(spec)
        H = P.from_expr(e)
        if P.variables(H) - set(checks.STENCIL5) - {"lam"}:
            raise P.Undecided("the update has free parameters")
        if a > 0:
            delta, how = P.add(P.var("u0"), P.var("um1"), -1), "D = 0, C_{i-1/2} = -(H - u_i)/(u_i - u_{i-1})"
        else:
            delta, how = P.add(P.var("up1"), P.var("u0"), -1), "C = 0, D_{i+1/2} = (H - u_i)/(u_{i+1} - u_i)"
        cs = cells(e)
        rows, failed, halves, pruned = [], [], 0, 0
        for c in cs["cells"]:
            if any(P.variables(x) & {"lam"} for x in c["atoms"]):
                raise P.Undecided("a sign-cell atom depends on dt/dx")
            N = _in_nu(P.add(c["poly"], P.var("u0"), -1), a)
            row = {"cell": [_show(x) for x in c["atoms"]], "H - u_i (in nu)": P.show(N), "halves": []}
            for s in (1, -1):
                sd = P.scale(delta, s)
                atoms = c["atoms"] + [sd]
                if lower_dimensional(atoms):
                    pruned += 1
                    continue
                halves += 1
                if a > 0:
                    goals = {"C >= 0": P.scale(N, -s), "C <= 1": P.scale(P.add(N, delta), s)}
                else:
                    goals = {"D >= 0": P.scale(N, s), "D <= 1": P.scale(P.add(delta, N, -1), s)}
                certs = {k: farkas_in_nu(g, atoms, lo, hi) for k, g in goals.items()}
                row["halves"].append({"sign": _show(sd), **{k: v or "none found" for k, v in certs.items()}})
                failed += [(len(rows), _show(sd), k) for k, v in certs.items() if v is None]
            rows.append(row)
    except checks.NonlinearFlux as ex:
        return result("tvd_harten", UNKNOWN, claim, f"{ex}: the nu-parametrised certificate needs f = a*u")
    except P.Undecided as ex:
        return result("tvd_harten", UNKNOWN, claim, str(ex))
    counts = {**cell_counts(cs), "halves certified (cell x sign of the difference)": halves,
              "halves pruned (lower-dimensional)": pruned}
    wit = {"nu": f"{a}*lam (a = {a})", "decomposition": how, "cell_counts": counts, "cover": COVER, "cells": rows}
    assumptions = [HARTEN, "the cells cover the state space (by construction, see cover)",
                   f"nu = a*dt/dx in [{lo}, {hi}]"]
    if failed:
        return result("tvd_harten", UNKNOWN, claim,
                      f"no certificate for {len(failed)} of the conditions (first: cell {failed[0][0]}, {failed[0][1]}, "
                      f"{failed[0][2]}); Harten's form is sufficient only, so this decides nothing", wit, assumptions)
    return result("tvd_harten", VERIFIED, claim,
                  f"Harten's conditions certified on every one of {halves} closed half-cells "
                  f"({len(cs['cells'])} sign cells, each split by the sign of the upwind difference) for every nu "
                  f"in [{lo}, {hi}]", wit, assumptions)


# ---------------------------------------------------------------- TVD: an explicit TV increase (necessary)

def evaluate(e, env: dict, memo=None) -> Fraction | None:
    """e at a rational point in Fraction arithmetic, straight from the expression (much faster than the
    normal form of a nested limiter, whose subexpressions are shared and evaluated once); None if a
    square root is irrational or a division is by 0."""
    memo = {} if memo is None else memo
    if id(e) in memo:
        return memo[id(e)][1]
    k, a = e.kind, e.args
    if k == "var": return Fraction(env[e.name])
    if k == "lit": return Fraction(e.q)
    vals = [evaluate(x, env, memo) for x in a]
    memo[id(e)] = (e, _apply(e, vals))
    return memo[id(e)][1]


def _apply(e, vals: list) -> Fraction | None:
    k = e.kind
    if None in vals:
        return None
    if k == "neg": return -vals[0]
    if k == "add": return vals[0] + vals[1]
    if k == "sub": return vals[0] - vals[1]
    if k == "mul": return vals[0] * vals[1]
    if k == "div": return vals[0] / vals[1] if vals[1] else None
    if k == "powi": return vals[0] ** e.q if vals[0] or e.q >= 0 else None
    if k == "sqrt": return P._exact_sqrt(vals[0]) if vals[0] >= 0 else None
    raise P.Undecided(f"{k} is outside the exact fragment")


def _step(e, u: list, lam: Fraction, flux=None) -> list | None:
    """One step on a periodic grid: from the update e, or, when the spec declares a numerical flux, as
    u_i - lam*(F_{i+1/2} - F_{i-1/2}) with each interface flux evaluated once (the same scheme:
    `checks.update` builds e from F exactly this way)."""
    n = len(u)
    if flux is not None:
        F = []
        for i in range(n):
            v = evaluate(flux, {**{x: u[(i + k) % n] for x, k in checks.FLUX_ARGS.items()}, "lam": lam})
            if v is None:
                return None
            F.append(v)
        return [u[i] - lam * (F[i] - F[i - 1]) for i in range(n)]
    out = []
    for i in range(n):
        v = evaluate(e, {**{x: u[(i + k) % n] for x, k in checks.OFFSET5.items()}, "lam": lam})
        if v is None:
            return None
        out.append(v)
    return out


def total_variation(u: list) -> Fraction:
    return sum((abs(u[(i + 1) % len(u)] - u[i]) for i in range(len(u))), Fraction(0))


def _candidates():
    """Periodic integer data: steps, spikes, steps with a shoulder, then a seeded random search."""
    for n in (6, 8):
        for k in range(1, n // 2 + 1):
            yield [0] * (n - k) + [1] * k
        yield [0] * (n - 1) + [1]
        yield [0] * (n - 2) + [1, 2]
        yield [0] * (n - 3) + [1, 2, 2]
        yield [0] * (n - 3) + [2, 1, 1]
    rng = random.Random(7)
    for _ in range(60):
        yield [rng.randint(-2, 2) for _ in range(rng.choice((5, 6, 7, 8)))]


def tv_increase(spec: dict) -> dict:
    """An exact refutation of TVD: a periodic rational state u^n and a rational nu in the claimed range
    with TV(u^{n+1}) > TV(u^n), all in Fraction arithmetic. A periodic grid of n cells is a valid state
    of the claim (and the same data repeated, or embedded in a long constant state, gives a compactly
    supported counterexample on the line). A failed search proves nothing: UNKNOWN, never VERIFIED."""
    r = _tvd_range(spec)
    if r is None:
        return result("tv_increase", NOT_APPLICABLE, "TVD", "no CFL range claimed (claims.tvd_cfl)")
    lo, hi = r
    claim = tvd_claim(r)
    try:
        a = _advection(spec)
        H = checks.update(spec)
        P.from_expr(H)                                           # in the fragment
        H = intern(H)
        flux = checks.numerical_flux(spec)
        flux = None if flux is None else intern(flux)
    except checks.NonlinearFlux as ex:
        return result("tv_increase", UNKNOWN, claim, f"{ex}: the search is parametrised by nu = a*dt/dx")
    except P.Undecided as ex:
        return result("tv_increase", UNKNOWN, claim, str(ex))
    nus = list(dict.fromkeys([lo + (hi - lo) * Fraction(t, 8) for t in (4, 8, 6, 2, 7, 1, 5, 3)]))
    nus = [x for x in nus if x / a > 0]                         # dt/dx = nu/a > 0
    tried = 0
    for data in _candidates():
        u = [Fraction(x) for x in data]
        tv0 = total_variation(u)
        for nu in nus:
            tried += 1
            v = _step(H, u, nu / a, flux)
            if v is None:
                continue
            tv1 = total_variation(v)
            if tv1 > tv0:
                wit = {"periodic state u^n": [str(x) for x in u], "nu": str(nu), "lam": str(nu / a),
                       "u^{n+1}": [str(x) for x in v], "TV(u^n)": str(tv0), "TV(u^{n+1})": str(tv1)}
                return result("tv_increase", REFUTED, claim,
                              f"TV grows from {tv0} to {tv1} in one step at nu = {nu} on the periodic state "
                              f"{[str(x) for x in u]}", wit,
                              ["periodic grid (the state repeated, or set in a long constant state, is a compactly "
                               "supported counterexample on the line)"])
    return result("tv_increase", UNKNOWN, claim,
                  f"no TV increase among {tried} (state, nu) pairs; a failed search proves nothing")


def max_principle_violation(spec: dict) -> dict:
    """An exact refutation of the local maximum principle min_k u_{i+k} <= u_i^{n+1} <= max_k u_{i+k}
    (k over the scheme's stencil, -2..2 at most): a periodic rational state and a nu in the claimed
    range (claims.tvd_cfl) with some u_i^{n+1} outside its stencil's range. The verifying side is
    `tvd_harten`: its certificate gives u_i^{n+1} = (1 - C) u_i + C u_{i-1} (or (1 - D) u_i + D u_{i+1})
    with C, D in [0, 1], a convex combination of two stencil values. A failed search proves nothing."""
    r = _tvd_range(spec)
    claim = (f"local maximum principle: u_i^{{n+1}} lies between the smallest and largest of u_{{i-2}}..u_{{i+2}} "
             f"for every state and every nu = a*dt/dx in [{r[0]}, {r[1]}]") if r else "local maximum principle"
    if r is None:
        return result("max_principle_violation", NOT_APPLICABLE, claim, "no CFL range claimed (claims.tvd_cfl)")
    lo, hi = r
    try:
        a = _advection(spec)
        H = checks.update(spec)
        ks = [checks.OFFSET5[x] for x in checks.STENCIL5 if x in P.variables(P.from_expr(H))]
        H = intern(H)
        flux = checks.numerical_flux(spec)
        flux = None if flux is None else intern(flux)
    except (checks.NonlinearFlux, P.Undecided) as ex:
        return result("max_principle_violation", UNKNOWN, claim, str(ex))
    nus = [x for x in dict.fromkeys([lo + (hi - lo) * Fraction(t, 8) for t in (4, 8, 6, 2, 7, 1, 5, 3)]) if x / a > 0]
    for data in _candidates():
        u = [Fraction(x) for x in data]
        for nu in nus:
            v = _step(H, u, nu / a, flux)
            if v is None:
                continue
            n = len(u)
            for i in range(n):
                st = [u[(i + k) % n] for k in range(min(ks), max(ks) + 1)]
                if not min(st) <= v[i] <= max(st):
                    wit = {"periodic state u^n": [str(x) for x in u], "nu": str(nu), "lam": str(nu / a), "i": i,
                           "u_i^{n+1}": str(v[i]), "stencil values": [str(x) for x in st]}
                    return result("max_principle_violation", REFUTED, claim,
                                  f"u_{i}^{{n+1}} = {v[i]} is outside [{min(st)}, {max(st)}], the range of its stencil, "
                                  f"at nu = {nu} on the periodic state {[str(x) for x in u]}", wit, ["periodic grid"])
    return result("max_principle_violation", UNKNOWN, claim, "no violation found; a failed search proves nothing")


# ---------------------------------------------------------------- truncation order per branch

def _linear_on_cell(p: P.Poly, a: Fraction) -> dict | None:
    """{offset: c_k(nu)} with p = sum_k c_k u_{i+k}, or None."""
    out: dict = {}
    for m, c in p.items():
        us = [(x, k) for x, k in m if x[0] == "v" and x[1] in checks.STENCIL5]
        if len(us) != 1 or us[0][1] != 1 or any(x[0] == "s" for x, _ in m):
            return None
        rest = _in_nu({P._mono({x: k for x, k in m if x != us[0][0]}): c}, a)
        if P.variables(rest) - {"nu"}:
            return None
        k = checks.OFFSET5[us[0][0][1]]
        out[k] = P.add(out.get(k, {}), rest)
    return out


DIFFS = {"Delta_{i+3/2}": ("up2", "up1"), "Delta_{i+1/2}": ("up1", "u0"), "Delta_{i-1/2}": ("u0", "um1"),
         "Delta_{i-3/2}": ("um1", "um2")}


def _named(L: P.Poly) -> str:
    if not L:
        return "0"
    for name, (x, y) in DIFFS.items():
        d = P.add(P.var(x), P.var(y), -1)
        for c in (1, 2, Fraction(1, 2), -1):
            if L == P.scale(d, c):
                return name if c == 1 else f"{c}*{name}"
    return P.show(L)


def _slopes(spec: dict, assign: dict, a: Fraction) -> dict:
    """The limited slope L at each interface on this cell, if the flux is in Sweby form
    F = a*uL + (a/2)(1 - a*lam)*L with L free of lam; else the cell flux itself."""
    F = checks.numerical_flux(spec)
    if F is None:
        return {}
    out = {}
    for name, shift, own in (("i+1/2", 0, "u0"), ("i-1/2", -1, "um1")):
        Fc = on_cell(substitute(F, checks._at_interface(shift)), assign)
        if Fc is None:
            out[name] = "not fixed by this cell"
            continue
        S = P.add(Fc, P.scale(P.var(own), a), -1)
        L = P.scale(P.subst(S, {"lam": P.const(0)}), 2 / a)
        sweby = P.mul(P.const(a / 2), P.add(P.const(1), P.scale(P.var("lam"), a), -1))
        out[name] = f"L = {_named(L)}" if P.add(S, P.mul(sweby, L), -1) == {} and not P.variables(L) & {"lam"} \
            else f"F = {P.show(Fc)}"
    return out


def _known(c: dict) -> str:
    """The textbook linear scheme (a > 0) this cell's update is, if any."""
    n = NU
    one = P.const(1)
    half = lambda p: P.scale(p, Fraction(1, 2))
    lw = {-1: half(P.mul(n, P.add(one, n))), 0: P.add(one, P.mul(n, n), -1), 1: half(P.mul(n, P.add(n, one, -1)))}
    bw = {-2: half(P.mul(n, P.add(n, one, -1))), -1: P.mul(n, P.add(P.const(2), n, -1)),
          0: half(P.mul(P.add(one, n, -1), P.add(P.const(2), n, -1)))}
    up = {-1: n, 0: P.add(one, n, -1)}
    clean = {k: v for k, v in c.items() if v}
    for name, ref in (("Lax-Wendroff", lw), ("Beam-Warming", bw), ("upwind", up)):
        if clean == {k: v for k, v in ref.items() if v}:
            return name
    return "mixed"


def branch_table(spec: dict) -> tuple[list, dict, Fraction]:
    """[(row, order)] per distinct cell polynomial, the cell decomposition, and a."""
    a = _advection(spec)
    e = checks.update(spec)
    cs = cells(e)
    seen: dict = {}
    for c in cs["cells"]:
        slopes = _slopes(spec, c["assign"], a)
        key = (checks._key(c["poly"]), str(slopes))
        if key in seen:
            seen[key]["cells"] += 1
            continue
        co = _linear_on_cell(c["poly"], a)
        if co is None:
            raise P.Undecided(f"the update is not linear on the cell {[_show(x) for x in c['atoms']]}")
        e_j = linear.truncation_terms(a, co, 2 + linear.MAX_EXTRA)
        lead = next((j for j, x in enumerate(e_j) if x), None)
        row = {"cell": [_show(x) for x in c["atoms"]], "slopes": slopes,
               "scheme": _known(co) if a > 0 else "", "coefficients": {str(k): P.show(v) for k, v in sorted(co.items())},
               "order": None if lead is None else lead - 1,
               "leading": None if lead is None else f"e_{lead} = {P.show(e_j[lead])}", "cells": 1}
        seen[key] = row
    return list(seen.values()), cs, a


def _p_smooth(spec: dict):
    c = spec.get("claims", {}).get("smooth_truncation")
    return None if c is None else c


def smooth_claim(p) -> str:
    return (f"pointwise truncation order {p}: the local truncation error is O(dx^{p}) at fixed dt/dx at every grid "
            "point, for every smooth exact solution (every stencil sampled from smooth data, extrema included)")


def truncation_branches(spec: dict) -> dict:
    """The exact truncation order of the linear scheme on each sign cell (the per-branch table).
    VERIFIED when every branch has order >= p: a stencil sampled from smooth data lies in some
    retained cell (they cover the space), where H is that branch's linear scheme, whose truncation
    error is O(dx^p) with a constant bounded by the data's derivatives; finitely many branches give a
    uniform bound. A branch of lower order does not refute (the data may never reach it): UNKNOWN."""
    c = _p_smooth(spec)
    if c is None:
        return result("truncation_branches", NOT_APPLICABLE, "pointwise truncation order", "not claimed (claims.smooth_truncation)")
    p = int(c["order"])
    claim = smooth_claim(p)
    try:
        rows, cs, a = branch_table(spec)
    except checks.NonlinearFlux as ex:
        return result("truncation_branches", UNKNOWN, claim, str(ex))
    except P.Undecided as ex:
        return result("truncation_branches", UNKNOWN, claim, str(ex))
    low = [r for r in rows if r["order"] is None or r["order"] < p]
    wit = {"nu": f"{a}*lam (a = {a})", "cell_counts": cell_counts(cs), "cover": COVER, "branches": rows}
    assumptions = ["u smooth (bounded derivatives)", "dt = lam*dx with lam fixed as dx -> 0",
                   "the cells cover the state space (by construction, see cover)"]
    if low:
        return result("truncation_branches", UNKNOWN, claim,
                      f"{len(low)} of {len(rows)} branches have truncation order below {p} (orders "
                      f"{sorted({r['order'] for r in low}, key=str)}); smooth data may or may not reach them", wit, assumptions)
    return result("truncation_branches", VERIFIED, claim,
                  f"every one of {len(rows)} branches is a linear scheme of truncation order >= {p}", wit, assumptions)


# ---------------------------------------------------------------- truncation on explicit smooth data (necessary)

DX = P.var("dx")
DATA = ("1 - x^2/2", "x^2/2 - 1", "x", "x^3")
PLACEMENTS = ("0", "1/2", "1/3")


def _sign_near_zero(p: P.Poly) -> int:
    """Sign of a polynomial in dx for all small dx > 0 (0 if p = 0)."""
    if not p:
        return 0
    lead = _lowest(p)[1]
    if set(lead) != {()}:
        raise P.Undecided("an atom's leading term in dx is not a number")
    return 1 if lead[()] > 0 else -1


def _lowest(p: P.Poly) -> tuple[int, P.Poly]:
    """(lowest power of dx in p, its coefficient)."""
    k = min(dict(m).get(("v", "dx"), 0) for m in p)
    return k, {P._mono({x: e for x, e in dict(m).items() if x != ("v", "dx")}): c for m, c in p.items()
               if dict(m).get(("v", "dx"), 0) == k}


def truncation_smooth_data(spec: dict) -> dict:
    """The local truncation error at explicit smooth data, exactly. For each polynomial exact solution
    u(x, t) = U(x - a t) (smooth: every derivative bounded on bounded sets) and grid placement
    x_i = theta*dx, the stencil u_{i+k} = U((theta + k) dx) is a polynomial in dx, so the sign of every
    cell atom is fixed for all small dx > 0 (for every dx > 0 when each atom is a single power of dx):
    the stencil lies in one cell, where H is a polynomial. Then
        tau(dx) = (U(theta dx - a dt) - H(stencil)) / dt,   dt = lam dx,
    is a Laurent polynomial in dx and nu, computed exactly. If its lowest power q < p has a coefficient
    that is non-zero (at an exact rational nu in the claimed range), tau is not O(dx^p): REFUTED. This
    is about the local truncation error only; it says nothing about the global error. Finding no such
    data proves nothing: UNKNOWN."""
    c = _p_smooth(spec)
    if c is None:
        return result("truncation_smooth_data", NOT_APPLICABLE, "pointwise truncation order", "not claimed (claims.smooth_truncation)")
    p = int(c["order"])
    claim = smooth_claim(p)
    try:
        a = _advection(spec)
        cs = cells(checks.update(spec))
    except (checks.NonlinearFlux, P.Undecided) as ex:
        return result("truncation_smooth_data", UNKNOWN, claim, str(ex))
    nus = [Fraction(x) for x in c.get("nu", ["1/2", "1/3", "3/4"])]
    rows = []
    for d in c.get("data", DATA):
        U = P.from_expr(parse(d))
        for th in c.get("placements", PLACEMENTS):
            th = Fraction(th)
            stencil = {x: P.subst(U, {"x": P.scale(DX, th + k)}) for x, k in checks.OFFSET5.items()}
            hit = None
            for cell in cs["cells"]:
                vals = [P.subst(at, stencil) for at in cell["atoms"]]
                try:
                    if all(_sign_near_zero(v) >= 0 for v in vals):
                        hit = cell, all(len(v) <= 1 for v in vals)
                        break
                except P.Undecided:
                    continue
            if hit is None:
                continue
            cell, every = hit
            Hc = P.subst(_in_nu(cell["poly"], a), stencil)
            exact = P.subst(U, {"x": P.mul(DX, P.add(P.const(th), NU, -1))})        # U(theta dx - nu dx)
            tau = P.mul(P.add(exact, Hc, -1), P.inverse(P.scale(P.mul(NU, DX), 1 / a)))  # dt = (nu/a) dx
            if not tau:
                rows.append({"data": d, "theta": str(th), "tau": "0"})
                continue
            q, lead = _lowest(tau)
            row = {"data U(x)": d, "placement x_i = theta*dx": str(th), "cell": [_show(x) for x in cell["atoms"]],
                   "stencil": {x: P.show(v) for x, v in stencil.items()}, "tau(dx)": P.show(tau),
                   "lowest power of dx": q, "its coefficient": P.show(lead),
                   "holds for": "every dx > 0" if every else "all sufficiently small dx > 0"}
            rows.append(row)
            if q < p:
                nu = next((x for x in nus if P.evaluate(lead, {"nu": x})), None)
                if nu is None:
                    continue
                v = P.evaluate(lead, {"nu": nu})
                row.update(nu=str(nu), coefficient_at_nu=str(v))
                return result("truncation_smooth_data", REFUTED, claim,
                              f"at u = U(x - a t), U(x) = {d}, x_i = {th}*dx, the stencil lies in the cell "
                              f"{row['cell']} for {row['holds for']}, and tau = {P.show(tau)}: its dx^{q} term is "
                              f"{v}*dx^{q} != 0 at nu = {nu}, so tau is not O(dx^{p})",
                              {"rows": rows, "cell_counts": cell_counts(cs)},
                              ["local truncation error only (no statement about the global error)",
                               "U is a polynomial, so u = U(x - a t) is an exact smooth solution of u_t + a u_x = 0",
                               "dt = lam*dx with nu = a*lam fixed"])
    return result("truncation_smooth_data", UNKNOWN, claim,
                  f"tau = O(dx^{p}) on all {len(rows)} (data, placement) pairs tried; a failed search proves nothing",
                  {"rows": rows})


# ---------------------------------------------------------------- monotonicity on five-point stencils

MONO_NUS = ("1/2", "1/4", "3/4", "1/8", "7/8", "1")          # fractions of the CFL bound tried for a refutation


def mono_claim(c) -> str:
    return (f"monotone: H(um2, um1, u0, up1, up2) is non-decreasing in each argument for lam > 0 and every "
            f"state, with nu = a*lam, |nu| <= {c}")


def nonneg_in_nu(c: list, lo: Fraction, hi: Fraction) -> list | None:
    """Pieces [(lo_k, hi_k, Bernstein coefficients)] covering [lo, hi], each with all coefficients >= 0, so
    the polynomial sum_j c_j nu^j is >= 0 on [lo, hi]; None if a sample is negative or bisection to
    MAX_DEPTH_NU finds no certificate."""
    out, todo = [], [(lo, hi, 0)]
    while todo:
        a0, b0, depth = todo.pop(0)
        b = checks.bernstein(list(c), a0, b0)
        if min(b) >= 0:
            out.append((a0, b0, b))
        elif depth >= MAX_DEPTH_NU or min(checks._horner(c, x) for x in (a0, (a0 + b0) / 2, b0)) < 0:
            return None
        else:
            m = (a0 + b0) / 2
            todo += [(a0, m, depth + 1), (m, b0, depth + 1)]
    return sorted(out, key=lambda t: t[0])


def cone_interior(atoms: list, names: list) -> dict | None:
    """A rational point where every homogeneous linear atom is > 0, so the closed cell is full-dimensional
    and the point is in its interior: small integers first, then an exact LP (phase 1 of the simplex
    method on a_j(p - q) - s_j = 1 with p, q, s >= 0), scaled to integers. Only a search: the caller
    re-checks every atom."""
    pt = _interior(atoms, names)
    if pt is not None or not atoms:
        return pt if pt is not None else {x: Fraction(0) for x in names}
    vecs = _lin_vectors(atoms, names)
    if vecs is None:
        return None
    m, n = len(atoms), len(names)
    cols = ([[v[i] for v in vecs] for i in range(n)] + [[-v[i] for v in vecs] for i in range(n)]
            + [[-Fraction(int(j == k)) for j in range(m)] for k in range(m)])
    mu = feasible(cols, [Fraction(1)] * m)
    if mu is None:
        return None
    x = [mu[i] - mu[n + i] for i in range(n)]
    den = lcm(*(v.denominator for v in x))
    return {name: v * den for name, v in zip(names, x)}


def _decreasing_pair(e, cell: dict, x: str, nu: Fraction, a: Fraction, stencil) -> dict | None:
    """States u <= v (v = u + h e_x), both strictly inside the cell, with H(u) > H(v) at nu, replayed by
    evaluating the update expression itself (not the cell polynomial) in Fraction arithmetic."""
    names = list(checks.STENCIL5)
    pt = cone_interior(cell["atoms"], names)
    if pt is None:
        return None
    u = {k: pt.get(k, Fraction(0)) for k in names}
    lins = [checks._linear(at, names) for at in cell["atoms"]]
    if None in lins:
        return None
    big = max((abs(la[1].get(x, Fraction(0))) for la in lins), default=Fraction(0))
    h = Fraction(1, 2 * (int(big) + 1))
    v = {**u, x: u[x] + h}
    lam = nu / a
    inside = lambda s: all(P.evaluate(at, s) > 0 for at in cell["atoms"])
    if not (inside(u) and inside(v)):
        return None
    Hu, Hv = evaluate(e, {**u, "lam": lam}), evaluate(e, {**v, "lam": lam})
    if Hu is None or Hv is None or not Hv < Hu:
        return None
    return {"nu": str(nu), "lam": str(lam), "u": {k: str(u[k]) for k in stencil}, "v": {k: str(v[k]) for k in stencil},
            "increased": x, "h": str(h), "H(u)": str(Hu), "H(v)": str(Hv), "H(u) - H(v)": str(Hu - Hv),
            "cell": [_show(at) for at in cell["atoms"]],
            "inside": "every atom of the cell is > 0 at u and at v (checked exactly)"}


def monotonicity_wide(spec: dict, stencil=checks.STENCIL5) -> dict:
    """Monotonicity of a limited (piecewise-polynomial) update of linear advection u_t + a u_x = 0 on the
    stencil u_{i-2}, ..., u_{i+2}: H non-decreasing in each argument for lam > 0 and |nu| = |a| lam <= c
    (c = claims.monotone_cfl; for f = a*u the CFL bound constrains lam only).

    Method. On each retained sign cell (`cells`; they cover the state space) H is a polynomial H_c,
    linear in the u's for the Sweby forms, so dH_c/du_k = c_k(nu) is a polynomial in nu alone; we
    certify c_k >= 0 on the closed nu-interval [0, c] (or [-c, 0] for a < 0) by Bernstein coefficients
    on a bisection (nu = 0 is outside the claim, so the interval is a superset: sound). A partial that
    still depends on the state is certified by `farkas_in_nu` on the cell. Non-negative partials on every
    closed cell give a non-decreasing H: H is continuous and piecewise polynomial, so along a coordinate
    line it is Lipschitz and the integral of its derivative, which is >= 0 off finitely many kinks (the
    argument in `checks.monotonicity`).

    REFUTED needs a real violation, not a derivative: a cell with an interior point (every atom > 0,
    checked exactly), a rational nu in the claimed range with c_k(nu) < 0, and two states u <= v that
    differ in u_k, both strictly inside that cell, with H(u) > H(v), replayed by evaluating the scheme's
    own expression in Fraction arithmetic. Past MAX_CELLS the check is UNKNOWN."""
    c = spec.get("claims", {}).get("monotone_cfl")
    if c is None:
        return result("monotonicity", NOT_APPLICABLE, "monotonicity", "no CFL bound claimed (claims.monotone_cfl)")
    c = Fraction(c)
    claim = mono_claim(c)
    assumptions = ["lam = dt/dx > 0", f"nu = a*lam with |nu| <= {c}"]
    try:
        a = _advection(spec)
        e = checks.update(spec)
        H = P.from_expr(e)
        if P.variables(H) - set(checks.STENCIL5) - {"lam"}:
            raise P.Undecided("the update has free parameters")
        lo, hi = (Fraction(0), c) if a > 0 else (-c, Fraction(0))
        cs = cells(e)
        rows, failed = [], []
        for k, cell in enumerate(cs["cells"]):
            if any(P.variables(x) & {"lam"} for x in cell["atoms"]):
                raise P.Undecided("a sign-cell atom depends on dt/dx")
            Hc = _in_nu(cell["poly"], a)
            row = {"cell": [_show(x) for x in cell["atoms"]], "H (in nu)": P.show(Hc), "partials": {}}
            for x in stencil:
                d = P.derivative(Hc, x)
                parts = _nu_parts(d)
                co = None
                if parts is not None and not P.variables(d) - {"nu"}:
                    co = [parts.get(j, {}).get((), Fraction(0)) for j in range(max(parts, default=0) + 1)]
                    pieces = nonneg_in_nu(co, lo, hi)
                    cert = None if pieces is None else {"bernstein_in_nu": [
                        {"nu": [str(p0), str(p1)], "min": str(min(b))} for p0, p1, b in pieces]}
                else:
                    cert = farkas_in_nu(d, cell["atoms"], lo, hi)
                row["partials"][x] = {f"dH/d{x}": P.show(d), "certificate": cert or "none found"}
                if cert is None:
                    failed.append((k, x, co))
            rows.append(row)
    except checks.NonlinearFlux as ex:
        return result("monotonicity", UNKNOWN, claim,
                      f"{ex}: the five-point monotonicity check covers linear advection f = a*u only",
                      assumptions=assumptions)
    except P.Undecided as ex:
        return result("monotonicity", UNKNOWN, claim, str(ex), assumptions=assumptions)
    wit = {"nu": f"{a}*lam (a = {a})", "nu interval certified": [str(lo), str(hi)], "cell_counts": cell_counts(cs),
           "cover": COVER, "cells": rows}
    assumptions += ["the cells cover the state space (by construction, see cover)",
                    "|x| = sqrt(x^2) is split into the cases x >= 0 and x <= 0"]
    if not failed:
        return result("monotonicity", VERIFIED, claim,
                      f"every partial dH/du_k is >= 0 on each of {len(rows)} closed sign cells for every nu in "
                      f"[{lo}, {hi}] (Bernstein certificates); H is continuous, so it is non-decreasing", wit, assumptions)
    ei = intern(e)
    nus = [t * (hi if a > 0 else lo) for t in map(Fraction, MONO_NUS)]
    for k, x, co in failed:
        for nu in nus if co is not None else ():
            if checks._horner(co, nu) >= 0:
                continue
            pair = _decreasing_pair(ei, cs["cells"][k], x, nu, a, stencil)
            if pair:
                wit["counterexample"] = {"cell index": k, f"dH/d{x} at nu": str(checks._horner(co, nu)), **pair}
                return result("monotonicity", REFUTED, claim,
                              f"u <= v (v = u + {pair['h']} in {x}) with H(u) = {pair['H(u)']} > H(v) = {pair['H(v)']} "
                              f"at nu = {nu}, both states strictly inside one sign cell, replayed from the scheme's "
                              "own expression", wit, assumptions)
    return result("monotonicity", UNKNOWN, claim,
                  f"no certificate for {len(failed)} (cell, argument) pairs and no replayed decreasing pair found",
                  wit, assumptions)
