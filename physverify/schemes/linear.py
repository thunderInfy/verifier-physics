"""Exact order of accuracy for linear constant-coefficient schemes u_i^{n+1} = sum_k c_k(nu) u_{i+k}^n
for u_t + a u_x = 0, nu = a*dt/dx: truncation error, von Neumann stability, and the scope of the
Lax-Richtmyer equivalence theorem that turns the two into a convergence order.

Truncation error. For a smooth exact solution u_t = -a u_x, so u(x, t + dt) = sum_j (-a dt)^j/j! u^(j)
and u(x + k dx, t) = sum_j (k dx)^j/j! u^(j). With dt = lam*dx, lam fixed, the local truncation error
tau = (u(x, t + dt) - sum_k c_k u(x + k dx, t))/dt is sum_j e_j(nu) dx^(j-1) u^(j), where

    e_j(nu) = a/(nu j!) * ((-nu)^j - sum_k c_k(nu) k^j).

The scheme is consistent of order p iff e_j = 0 (as a function of nu) for j <= p. The first non-zero
e_j gives the modified equation u_t + a u_x = -e_j dx^(j-1) u^(j) + ...: dispersive for odd j,
diffusive or anti-diffusive for even j by its sign.

Von Neumann. The amplification factor is g(theta) = sum_k c_k e^{i k theta}; with real c_k,
|g|^2 = sum_k c_k^2 + 2 sum_{k<l} c_k c_l cos((l - k) theta), a polynomial in nu and z = cos(theta)
through Chebyshev polynomials. We certify G = 1 - |g|^2 >= 0 on nu in [lo, hi], z in [-1, 1]: strip
the factors (1 - z) and (1 + z), which are >= 0 there, then check the tensor-product Bernstein
coefficients of the rest on the box, bisecting the box when some are negative. REFUTED needs an exact
rational (nu, z) in the box with G < 0.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial

from . import checks, poly as P
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

OFFSET = {"um1": -1, "u0": 0, "up1": 1}
NU, Z = P.var("nu"), P.var("z")
MAX_EXTRA = 8          # how far past p+1 we look for the leading term
MAX_BOXES = 256        # bisection budget for the von Neumann certificate


def coefficients(spec: dict, check: str, claim: str) -> tuple[tuple | None, dict | None]:
    """((a, {offset k: c_k(nu)}), None) for a linear constant-coefficient scheme, else (None, result)."""
    try:
        a, c = checks.linear_coefficients(spec)
    except checks.NotLinear as ex:
        return None, result(check, NOT_APPLICABLE, claim, f"{ex}: this check covers linear schemes only")
    except P.Undecided as ex:
        return None, result(check, UNKNOWN, claim, str(ex))
    stray = set().union(*(P.variables(p) for p in c.values())) - {"nu"}
    if stray:
        return None, result(check, NOT_APPLICABLE, claim,
                            f"coefficients depend on {sorted(stray)}, not only on nu: not constant-coefficient")
    if not a:
        return None, result(check, NOT_APPLICABLE, claim, "a = 0: nu = a*lam carries no information about lam")
    return (a, {OFFSET[k]: p for k, p in c.items()}), None


def _show_coefficients(c: dict) -> dict:
    return {name: P.show(c.get(k, {})) for name, k in OFFSET.items()}


# ---------------------------------------------------------------- truncation error

def truncation_terms(a: Fraction, c: dict, jmax: int) -> list:
    """[e_0, ..., e_jmax] as Polys in nu (Laurent: e_j carries a factor 1/nu)."""
    out = []
    for j in range(jmax + 1):
        m = {}
        for k, p in c.items():
            m = P.add(m, P.scale(p, Fraction(k) ** j))
        d = P.add(P.scale(P.power(NU, j), (-1) ** j), m, -1)
        out.append(P.scale(P.mul(d, P.inverse(NU)), a / factorial(j)))
    return out


def _sample_nus(spec: dict) -> list:
    """Rational nu to evaluate at: inside the claimed von Neumann range first, then generic values."""
    r = spec.get("claims", {}).get("von_neumann_cfl")
    out = []
    if r:
        lo, hi = (Fraction(x) for x in r)
        out += [lo + (hi - lo) * Fraction(t, 16) for t in (8, 4, 12, 2, 14, 1, 15, 16, 0)]
    out += [Fraction(1, 2), Fraction(1, 3), Fraction(-1, 2), Fraction(2), Fraction(3, 7)]
    return [x for x in dict.fromkeys(out) if x]


def _kind(j: int, e: P.Poly, nu: Fraction) -> str:
    """The leading term -e_j dx^(j-1) u^(j) of the modified equation: dispersive for odd j; for even j,
    diffusive when (-1)^(j/2 + 1) * (-e_j) > 0 (so u_t = mu u_xx, mu > 0, or u_t = -mu u_xxxx, ...)."""
    if j % 2:
        return "dispersive"
    s = (-1) ** (j // 2 + 1) * -P.evaluate(e, {"nu": nu})
    return f"{'diffusive' if s > 0 else 'anti-diffusive' if s < 0 else 'vanishes'} at nu = {nu}"


def truncation_order(spec: dict) -> dict:
    p = spec.get("claims", {}).get("consistent_order")
    if p is None:
        return result("truncation_order", NOT_APPLICABLE, "truncation order", "no order claimed (claims.consistent_order)")
    p = int(p)
    claim = (f"consistent of order {p}: the local truncation error is O(dx^{p}) at fixed lam = dt/dx "
             f"(e_j(nu) = 0 for j <= {p})")
    got, bad = coefficients(spec, "truncation_order", claim)
    if bad:
        return bad
    a, c = got
    e = truncation_terms(a, c, p + 1 + MAX_EXTRA)
    lead = next((j for j, ej in enumerate(e) if ej), None)
    nus = _sample_nus(spec)
    wit = {"nu": f"{a}*lam (a = {a})", "coefficients": _show_coefficients(c),
           "tau": "sum_j e_j(nu) dx^(j-1) d^j u/dx^j, e_j = a/(nu j!) ((-nu)^j - sum_k c_k k^j)",
           "e_j": {j: P.show(ej) for j, ej in enumerate(e[:max(p + 2, (lead or 0) + 1)])}}
    assumptions = ["u smooth (bounded derivatives up to order p + 2)", "dt = lam*dx with lam fixed as dx -> 0",
                   "the e_j are identities in nu, so the order holds for every lam != 0 (no CFL bound needed)"]
    if lead is None:
        return result("truncation_order", UNKNOWN, claim,
                      f"e_j = 0 for every j <= {len(e) - 1}: no leading term found", wit, assumptions)
    hit = next(((nu, v) for nu in nus if (v := P.evaluate(e[lead], {"nu": nu}))), None)
    order = lead - 1
    if hit is None:                                     # a non-zero Laurent polynomial has a non-root among these
        return result("truncation_order", UNKNOWN, claim, f"e_{lead} = {P.show(e[lead])} not decided", wit, assumptions)
    nu, v = hit
    wit["leading_term"] = {"j": lead, "e_j": P.show(e[lead]),
                           "modified_equation": f"u_t + a u_x = ({P.show(P.scale(e[lead], -1))})*dx^{lead - 1}*d^{lead}u/dx^{lead} + ...",
                           "kind": _kind(lead, e[lead], nus[0])}
    wit["order"] = order
    if order < p:
        wit.update(offending_j=lead, nu_value=str(nu), lam_value=str(nu / a), e_j_value=str(v))
        return result("truncation_order", REFUTED, claim,
                      f"e_{lead} = {P.show(e[lead])} is {v} != 0 at nu = {nu} (lam = {nu / a}): the scheme is "
                      f"consistent of order {order}, not {p}", wit, assumptions)
    more = "" if order == p else f"; e_{p + 1} vanishes too, so the order is {order}, higher than claimed (the claim is 'at least {p}')"
    return result("truncation_order", VERIFIED, claim,
                  f"e_0..e_{p} are identically 0 in nu; leading term e_{lead} = {P.show(e[lead])}" + more, wit, assumptions)


# ---------------------------------------------------------------- von Neumann

def _chebyshev(n: int) -> P.Poly:
    t0, t1 = P.const(1), Z
    for _ in range(n):
        t0, t1 = t1, P.add(P.scale(P.mul(Z, t1), 2), t0, -1)
    return t0


def amplification_squared(c: dict) -> P.Poly:
    """|g|^2 in nu and z = cos(theta), for real coefficients c_k(nu)."""
    ks = sorted(c)
    g2 = {}
    for i, k in enumerate(ks):
        g2 = P.add(g2, P.mul(c[k], c[k]))
        for l in ks[i + 1:]:
            g2 = P.add(g2, P.scale(P.mul(P.mul(c[k], c[l]), _chebyshev(l - k)), 2))
    return g2


def _grid(p: P.Poly) -> list | None:
    """p as rows over z of coefficient lists over nu: p = sum_j sum_i g[j][i] nu^i z^j (None if not a polynomial)."""
    if P.variables(p) - {"nu", "z"}:
        return None
    deg = {"nu": 0, "z": 0}
    for m in p:
        for x, k in m:
            if k < 0:
                return None
            deg[x[1]] = max(deg[x[1]], k)
    g = [[Fraction(0)] * (deg["nu"] + 1) for _ in range(deg["z"] + 1)]
    for m, v in p.items():
        d = {x[1]: k for x, k in m}
        g[d.get("z", 0)][d.get("nu", 0)] += v
    return g


def _divide_z(g: list, r: int) -> list | None:
    """q with g = (z - r) q, or None if g(z = r) is not identically 0 in nu."""
    n = len(g) - 1
    if n < 1:
        return None
    q = [None] * n
    q[n - 1] = list(g[n])
    for j in range(n - 1, 0, -1):
        q[j - 1] = [a + r * b for a, b in zip(g[j], q[j])]
    if any(a + r * b for a, b in zip(g[0], q[0])):
        return None
    return q


def _bernstein_fixed(c: list, lo: Fraction, hi: Fraction) -> list:
    """Bernstein coefficients of the polynomial with power coefficients c, on [lo, hi], degree len(c) - 1."""
    a = checks._compose_affine(c, lo, hi - lo)[:len(c)]
    n = len(c) - 1
    return [sum(Fraction(comb(k, j), comb(n, j)) * a[j] for j in range(k + 1)) for k in range(n + 1)]


def tensor_bernstein(g: list, nu: tuple, z: tuple) -> list:
    """Tensor-product Bernstein coefficients b[j][i] of g on the box nu x z; all >= 0 certifies g >= 0 there."""
    rows = [_bernstein_fixed(row, *nu) for row in g]                         # along nu, per power of z
    cols = [_bernstein_fixed([rows[j][i] for j in range(len(g))], *z) for i in range(len(g[0]))]
    return [[cols[i][j] for i in range(len(g[0]))] for j in range(len(g))]


def _value(g: list, nu: Fraction, z: Fraction) -> Fraction:
    return sum((v * nu ** i * z ** j for j, row in enumerate(g) for i, v in enumerate(row)), Fraction(0))


def _certify_box(g: list, nu: tuple, z: tuple) -> tuple[list | None, list]:
    """(certified boxes with their coefficients, or None; the boxes still failing when the budget ran out)."""
    todo, done = [(nu, z)], []
    while todo:
        if len(done) + len(todo) > MAX_BOXES:
            return None, todo
        bn, bz = todo.pop(0)
        b = tensor_bernstein(g, bn, bz)
        if min(min(row) for row in b) >= 0:
            done.append({"nu": [str(x) for x in bn], "z": [str(x) for x in bz],
                         "bernstein": [[str(x) for x in row] for row in b]})
            continue
        wn, wz = (bn[1] - bn[0]), (bz[1] - bz[0]) / 2      # z spans 2, so compare relative widths
        if wn >= wz and wn > 0:
            m = (bn[0] + bn[1]) / 2
            todo += [((bn[0], m), bz), ((m, bn[1]), bz)]
        elif wz > 0:
            m = (bz[0] + bz[1]) / 2
            todo += [(bn, (bz[0], m)), (bn, (m, bz[1]))]
        else:
            return None, [(bn, bz)]
    return done, []


def von_neumann(spec: dict) -> dict:
    r = spec.get("claims", {}).get("von_neumann_cfl")
    if r is None:
        return result("von_neumann", NOT_APPLICABLE, "von Neumann stability", "no CFL range claimed (claims.von_neumann_cfl)")
    lo, hi = (Fraction(x) for x in r)
    claim = f"von Neumann stable: |g(theta)|^2 <= 1 for every theta and every nu = a*dt/dx in [{lo}, {hi}]"
    if lo > hi:
        return result("von_neumann", UNKNOWN, claim, "empty CFL range")
    got, bad = coefficients(spec, "von_neumann", claim)
    if bad:
        return bad
    a, c = got
    g2 = amplification_squared(c)
    G = P.add(P.const(1), g2, -1)
    wit = {"nu": f"{a}*lam (a = {a})", "coefficients": _show_coefficients(c), "z": "cos(theta)",
           "|g|^2": P.show(g2), "1 - |g|^2": P.show(G)}
    assumptions = ["periodic grid, constant coefficients: Fourier modes decouple, so |g| <= 1 is l2 stability",
                   "g depends on theta and nu only (not on dt), so |g| <= 1 is the von Neumann condition itself"]
    grid = _grid(G)
    if grid is None:
        return result("von_neumann", UNKNOWN, claim, "1 - |g|^2 is not a polynomial in nu and z", wit, assumptions)
    q, factors = grid, {"1 - z": 0, "1 + z": 0}
    for name, root, sign in (("1 - z", 1, -1), ("1 + z", -1, 1)):    # 1 - z = -(z - 1), 1 + z = (z + 1)
        while (d := _divide_z(q, root)) is not None:
            q, factors[name] = [[sign * x for x in row] for row in d], factors[name] + 1
    Q = {}
    for j, row in enumerate(q):
        for i, v in enumerate(row):
            Q = P.add(Q, P.scale(P.mul(P.power(NU, i), P.power(Z, j)), v))
    wit["factored"] = (" * ".join(f"({f})^{k}" for f, k in factors.items() if k) + " * Q").lstrip(" *")
    wit["Q"] = P.show(Q)
    boxes, failing = _certify_box(q, (lo, hi), (Fraction(-1), Fraction(1)))
    if boxes is not None:
        wit["certificate"] = {"boxes": boxes, "rule": "every tensor Bernstein coefficient of Q on each box is >= 0, "
                              "and the boxes cover [lo, hi] x [-1, 1]; the stripped factors are >= 0 for z in [-1, 1]"}
        return result("von_neumann", VERIFIED, claim,
                      f"1 - |g|^2 = {wit['factored']} with Q >= 0 certified on {len(boxes)} box(es)", wit, assumptions)
    # simple points first: the ends and middle of the range, z = 0, then finer grids, then the failing boxes
    nus = list(dict.fromkeys([hi, lo, (lo + hi) / 2] + [lo + (hi - lo) * Fraction(t, 32) for t in range(33)]))
    zs = list(dict.fromkeys([Fraction(0), Fraction(1, 2), Fraction(-1, 2)] + [Fraction(t, 16) for t in range(-16, 17)]))
    pts = [(n, z) for n in nus for z in zs] + [((bn[0] + bn[1]) / 2, (bz[0] + bz[1]) / 2) for bn, bz in failing]
    for n, z in pts:
        v = _value(grid, n, z)
        if v < 0:
            wit["counterexample"] = {"nu": str(n), "lam": str(n / a), "z = cos(theta)": str(z),
                                     "|g|^2": str(1 - v), "1 - |g|^2": str(v)}
            return result("von_neumann", REFUTED, claim,
                          f"|g|^2 = {1 - v} > 1 at nu = {n} (lam = {n / a}), cos(theta) = {z}", wit, assumptions)
    return result("von_neumann", UNKNOWN, claim,
                  f"no Bernstein certificate within {MAX_BOXES} boxes and no rational point with |g|^2 > 1 found",
                  wit, assumptions)


# ---------------------------------------------------------------- scope of Lax-Richtmyer

SMOOTH_PROBLEMS = ("advection-sine",)


def lax_richtmyer_scope(spec: dict) -> dict:
    """Structural precondition for reading consistency + stability as convergence (Lax-Richtmyer):
    a linear constant-coefficient scheme, a convergence claim that is about refining dx at fixed dt/dx
    (the combined study) at the consistency order claimed, run at a dt/dx inside the claimed von Neumann
    range, on smooth data. VERIFIED when all hold; NOT_APPLICABLE (never a failure) otherwise."""
    claim = "Lax-Richtmyer applies: linear constant-coefficient scheme, combined refinement at a stable dt/dx, smooth data"
    got, bad = coefficients(spec, "lax_richtmyer_scope", claim)
    if bad:
        return result("lax_richtmyer_scope", NOT_APPLICABLE, claim, bad["detail"])
    a, _ = got
    cl, test = spec.get("claims", {}), spec.get("test", {})
    order, p, r = cl.get("order", {}), cl.get("consistent_order"), cl.get("von_neumann_cfl")
    why = []
    if set(order) != {"combined"}:
        why.append(f"claimed studies {sorted(order)}: the theorem covers refining dx at fixed dt/dx (combined) only")
    if p is None or order.get("combined") != p:
        why.append(f"combined order {order.get('combined')} is not the claimed consistency order {p}")
    nu = a * Fraction(str(test["lam"])) if "lam" in test else None
    if r is None or nu is None or not Fraction(r[0]) <= nu <= Fraction(r[1]):
        why.append(f"the study's nu = {nu} is not inside the claimed von Neumann range {r}")
    if test.get("problem", {}).get("kind") not in SMOOTH_PROBLEMS:
        why.append("the test problem is not one of the smooth ones " + str(SMOOTH_PROBLEMS))
    if why:
        return result("lax_richtmyer_scope", NOT_APPLICABLE, claim, "; ".join(why))
    return result("lax_richtmyer_scope", VERIFIED, claim, "every precondition holds (structural, exact)",
                  {"a": str(a), "nu of the study": str(nu), "von Neumann range": [str(x) for x in r],
                   "order": p, "problem": test["problem"]["kind"]})
