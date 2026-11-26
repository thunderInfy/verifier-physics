"""Exact structural checks for 1D three-point schemes u_t + f(u)_x = 0.

Stencil variables: um1, u0, up1 (u_{i-1}^n, u_i^n, u_{i+1}^n) and lam = dt/dx. A numerical
flux F is written in uL, uR. Every check returns a plain dict with an explicit witness
(a normal form, a recovered flux, a coefficient list, or an exact rational counterexample),
so each verdict can later be replayed as a Lean certificate.

The entropy check (`entropy_stability`) is Tadmor's semi-discrete inequality: exact, but it says
nothing about the time discretisation.

Statuses: VERIFIED (exact identity or exact inequality certificate), REFUTED (exact rational
counterexample, re-evaluated in Fraction arithmetic), UNKNOWN (outside the decided fragment),
NOT_APPLICABLE. No verdict here ever rests on a floating-point number.
"""

from __future__ import annotations

import random
from fractions import Fraction
from itertools import combinations
from math import comb

from ..expr import E, diff, lit, parse, substitute, to_str, var
from . import poly as P

VERIFIED, REFUTED, UNKNOWN, NOT_APPLICABLE = "VERIFIED", "REFUTED", "UNKNOWN", "NOT_APPLICABLE"
EXACT = "exact (Python Fraction arithmetic; Lean certificate pending)"
STENCIL = ("um1", "u0", "up1")


def result(check, status, claim, detail="", witness=None, assumptions=()):
    return {"check": check, "status": status, "guarantee": EXACT if status in (VERIFIED, REFUTED) else "",
            "claim": claim, "detail": detail, "witness": witness or {}, "assumptions": list(assumptions)}


def _expr(spec: dict, s: str) -> E:
    return substitute(parse(s), {k: lit(Fraction(v)) for k, v in spec.get("params", {}).items()})


def pde_flux(spec: dict) -> E:
    return _expr(spec, spec["pde"]["flux"])


def numerical_flux(spec: dict) -> E | None:
    s = spec["scheme"].get("numerical_flux")
    return _expr(spec, s) if s else None


def update(spec: dict) -> E:
    """u_i^{n+1} as an expression in um1, u0, up1, lam."""
    F = numerical_flux(spec)
    if F is None:
        return _expr(spec, spec["scheme"]["update"])
    at = lambda l, r: substitute(F, {"uL": var(l), "uR": var(r)})
    return E("sub", (var("u0"), E("mul", (var("lam"), E("sub", (at("u0", "up1"), at("um1", "u0")))))))


def _points(names, n=200, seed=0):
    rng = random.Random(seed)
    yield {v: Fraction(1) for v in names}
    for _ in range(n):
        yield {v: Fraction(rng.choice([1, -1]) * rng.randint(1, 9), rng.randint(1, 4)) for v in names}


def _nonzero_point(p: P.Poly, extra=()):
    """An exact rational point where p evaluates to a non-zero value, or None."""
    names = sorted(P.variables(p) | set(extra))
    for pt in _points(names):
        v = P.evaluate(p, pt)
        if v:
            return pt, v
    return None


def _fmt(pt: dict) -> dict:
    return {k: str(v) for k, v in pt.items()}


# ---------------------------------------------------------------- conservation

def telescoping(H: P.Poly) -> tuple[P.Poly, P.Poly]:
    """Candidate flux potential Phi(x, y) with H - u0 = Phi(u0, up1) - Phi(um1, u0).

    If such Phi exists for D = H - u0, then D(0, x, y) + D(0, 0, x) = Phi(x, y) - Phi(0, 0),
    so this candidate is the only one up to a constant. Returns (Phi, residual); the update is
    in flux form exactly when the residual normal form is 0.
    """
    D = P.add(H, P.var("u0"), -1)
    z, x, y = P.const(0), P.var("_x"), P.var("_y")
    phi = P.add(P.subst(D, {"um1": z, "u0": x, "up1": y}), P.subst(D, {"um1": z, "u0": z, "up1": x}))
    at = lambda a, b: P.subst(phi, {"_x": P.var(a), "_y": P.var(b)})
    return phi, P.add(D, P.add(at("u0", "up1"), at("um1", "u0"), -1), -1)


def periodic_change(H: P.Poly, state: list, lam) -> Fraction | None:
    """sum_i (u_i^{n+1} - u_i^n) on a periodic grid, exactly (None if a sqrt is irrational)."""
    n, total = len(state), Fraction(0)
    for i in range(n):
        v = P.evaluate(H, {"um1": state[i - 1], "u0": state[i], "up1": state[(i + 1) % n], "lam": lam})
        if v is None:
            return None
        total += v - state[i]
    return total


def conservation(spec: dict) -> dict:
    claim = "discrete conservation on a periodic grid: sum_i (u_i^{n+1} - u_i^n) = 0"
    try:
        H = P.from_expr(update(spec))
        phi, residual = telescoping(H)
    except P.Undecided as ex:
        return result("conservation", UNKNOWN, claim, str(ex))
    if not residual:
        F = P.scale(P.mul(P.subst(phi, {"_x": P.var("uL"), "_y": P.var("uR")}), P.inverse(P.var("lam"))), -1)
        rng = random.Random(1)
        state = [Fraction(rng.randint(-20, 20), rng.randint(1, 7)) for _ in range(7)]
        return result("conservation", VERIFIED, claim,
                      "update telescopes: u_i^{n+1} - u_i^n = -lam*(F(u_i, u_{i+1}) - F(u_{i-1}, u_i))",
                      {"recovered_flux": P.show(F), "flux_potential_Phi(_x,_y)": P.show(phi),
                       "residual_normal_form": "0",
                       "spot_check": {"state": [str(s) for s in state], "lam": "1/3",
                                      "sum_change": str(periodic_change(H, state, Fraction(1, 3)))}},
                      ["lam = dt/dx != 0"])
    rng = random.Random(2)
    for n in (3, 4, 5, 6):
        for _ in range(50):
            state = [Fraction(rng.randint(-9, 9), rng.randint(1, 3)) for _ in range(n)]
            lam = Fraction(rng.randint(1, 4), rng.randint(1, 4))
            d = periodic_change(H, state, lam)
            if d:
                return result("conservation", REFUTED, claim,
                              f"update is not in flux form (telescoping residual {P.show(residual)}); "
                              f"total changes by {d} on the periodic state below",
                              {"telescoping_residual": P.show(residual), "state": [str(s) for s in state],
                               "lam": str(lam), "sum_change": str(d)})
    return result("conservation", UNKNOWN, claim,
                  f"telescoping residual {P.show(residual)} is non-zero but no counterexample found")


# ---------------------------------------------------------------- consistency

def consistency(spec: dict) -> dict:
    claim = "consistency: F(u, u) = f(u)"
    try:
        f = P.from_expr(pde_flux(spec))
        F = numerical_flux(spec)
        if F is not None:
            F, how = P.from_expr(F), "declared numerical flux"
        else:
            phi, residual = telescoping(P.from_expr(update(spec)))
            if residual:
                return result("consistency", NOT_APPLICABLE, claim, "update is not in flux form, so it has no numerical flux")
            F = P.scale(P.mul(P.subst(phi, {"_x": P.var("uL"), "_y": P.var("uR")}), P.inverse(P.var("lam"))), -1)
            F = P.add(F, P.const(P.evaluate(f, {"u": 0}) - (P.evaluate(F, {"uL": 0, "uR": 0, "lam": 1}) or 0)))
            how = "flux recovered from the update (fixed up to a constant by F(0,0) = f(0))"
        Fuu = P.subst(F, {"uL": P.var("u"), "uR": P.var("u")})
        r = P.add(Fuu, f, -1)
    except P.Undecided as ex:
        return result("consistency", UNKNOWN, claim, str(ex))
    wit = {"F(u,u)": P.show(Fuu), "f(u)": P.show(f), "residual_normal_form": P.show(r), "flux": how}
    if not r:
        return result("consistency", VERIFIED, claim, "F(u,u) - f(u) normalizes to 0", wit,
                      ["sqrt arguments are sums of even powers, so sqrt(p)^2 = p"] if "sqrt" in wit["F(u,u)"] else [])
    hit = _nonzero_point(r)
    if hit is None:
        return result("consistency", UNKNOWN, claim, f"residual {P.show(r)} not decided", wit)
    pt, v = hit
    wit.update(point=_fmt(pt), residual_value=str(v))
    return result("consistency", REFUTED, claim, f"F(u,u) - f(u) = {v} at {_fmt(pt)}", wit)


# ---------------------------------------------------------------- entropy stability (semi-discrete, Tadmor)

SEMI_DISCRETE = ("semi-discrete only: the inequality is for the method of lines du_i/dt = -(F_{i+1/2} - F_{i-1/2})/dx; "
                 "the time discretisation is not covered (forward Euler can produce entropy), so the fully "
                 "discrete scheme is not certified")
ENTROPY_EXACT = EXACT + "; semi-discrete inequality only, time stepping not certified"
_VALUES = [Fraction(x) for x in (0, 1, -1, 2, -2, "1/2", "-1/2", 3, -3, "1/3", "-1/3", "3/2", "-3/2")]


def entropy_pair(spec: dict) -> tuple[E, E, str]:
    """(eta, q) in u: declared in claims.entropy, or (u^2/2, u^3/3) when the flux is Burgers' u^2/2."""
    c = spec["claims"]["entropy_stability"]
    if "eta" in c:
        return _expr(spec, c["eta"]), _expr(spec, c["q"]), "declared"
    if P.add(P.from_expr(pde_flux(spec)), P.from_expr(parse("u^2/2")), -1):
        raise P.Undecided("no entropy pair declared and the flux is not Burgers' u^2/2")
    return parse("u^2/2"), parse("u^3/3"), "default for Burgers"


def _key(p: P.Poly) -> tuple:
    return tuple(sorted(p.items(), key=P._key))


class _Split(Exception):
    def __init__(self, p):
        self.p = p


def sign_cells(e: E) -> list[tuple[P.Poly, list]]:
    """Split every |x| = sqrt(x^(2k)) in e into sign cases. Returns [(poly, atoms)]: on the closed
    cell {a >= 0 for a in atoms} the expression equals poly, and the cells cover every (uL, uR).
    The same |x| (or |-x|) gets the same sign throughout, so nested and repeated atoms are consistent."""
    def hook(assign):
        def h(node, rec):
            a = node.args[0]
            if a.kind != "powi" or a.q % 2:
                raise P.Undecided("square root of something other than an even power")
            x = P.power(rec(a.args[0]), a.q // 2)
            if set(x) <= {()}:
                return P.const(abs(x.get((), Fraction(0))))
            for key, sgn in ((_key(x), 1), (_key(P.scale(x, -1)), -1)):
                if key in assign:
                    return P.scale(x, sgn * assign[key][1])
            raise _Split(x)
        return h
    todo, out = [{}], []
    while todo:
        assign = todo.pop(0)
        try:
            p = P.from_expr(e, hook(assign))
        except _Split as s:
            todo += [{**assign, _key(s.p): (s.p, sgn)} for sgn in (1, -1)]
            continue
        out.append((p, [P.scale(x, sgn) for x, sgn in assign.values()]))
    return out


def _affine(a: P.Poly):
    """(cL, cR, c0) with a = cL*uL + cR*uR + c0 and the c's free of uL, uR; None if a is not affine."""
    out = {"uL": {}, "uR": {}, "": {}}
    for m, c in a.items():
        d = dict(m)
        if any(x[0] == "s" and P.variables(dict(x[1])) & {"uL", "uR"} for x in d):
            return None
        eL, eR = d.pop(("v", "uL"), 0), d.pop(("v", "uR"), 0)
        if eL < 0 or eR < 0 or eL + eR > 1:
            return None
        k = "uL" if eL else "uR" if eR else ""
        out[k] = P.add(out[k], {P._mono(d): c})
    return out["uL"], out["uR"], out[""]


def _change_of_variables(c1, c2):
    """uL, uR in terms of _s = a1 and _t = a2 (a1, a2 affine), if the determinant is a monomial."""
    (l1, r1, o1), (l2, r2, o2) = c1, c2
    det = P.add(P.mul(l1, r2), P.mul(r1, l2), -1)
    if not det:
        return None
    try:
        inv = P.inverse(det)
    except P.Undecided:
        return None
    s, t = P.add(P.var("_s"), o1, -1), P.add(P.var("_t"), o2, -1)
    return {"uL": P.mul(inv, P.add(P.mul(r2, s), P.mul(r1, t), -1)),
            "uR": P.mul(inv, P.add(P.mul(l1, t), P.mul(l2, s), -1))}


def certify_nonneg(T: P.Poly, atoms: list) -> dict | None:
    """A certificate that T >= 0 on {a >= 0 for a in atoms} (lam > 0), or None.

    Either T is non-negative by its form (positive coefficients, even powers of uL and uR, any
    power of lam, square roots), or after the linear change of variables _s = a1, _t = a2 it is
    non-negative by form with _s >= 0 and, if a2 is an atom, _t >= 0 (otherwise a2 is one of the
    free coordinates uL, uR, uR - uL and _t must occur to even powers)."""
    if P.nonneg_by_form(T, positive={"lam"}):
        return {"coordinates": "uL, uR", "in_coordinates": P.show(T)}
    free = [P.var("uL"), P.var("uR"), P.add(P.var("uR"), P.var("uL"), -1)]
    cands = [(a, _affine(a), True) for a in atoms] + [(a, _affine(a), False) for a in free]
    cands = [x for x in cands if x[1] is not None]
    for i, (a1, c1, n1) in enumerate(cands):
        if not n1:
            break
        for a2, c2, n2 in cands[i + 1:]:
            sub = _change_of_variables(c1, c2)
            if sub is None:
                continue
            T2 = P.subst(T, sub)
            if P.nonneg_by_form(T2, nonneg={"_s"} | ({"_t"} if n2 else set()), positive={"lam"}):
                return {"coordinates": f"_s = {P.show(a1)} >= 0, _t = {P.show(a2)}" + (" >= 0" if n2 else " (free)"),
                        "uL": P.show(sub["uL"]), "uR": P.show(sub["uR"]), "in_coordinates": P.show(T2)}
    return None


def _cfl_atoms(spec: dict) -> list:
    c = spec["claims"]["entropy_stability"].get("cfl")
    if c is None:
        return []
    c = P.const(Fraction(c))
    return [P.add(c, P.mul(P.var("lam"), P.var(x)), s) for x in ("uL", "uR") for s in (-1, 1)]


def _show_atom(a: P.Poly) -> str:
    return f"{P.show(a)} >= 0"


def entropy_stability(spec: dict) -> dict:
    """Tadmor's semi-discrete entropy-stability test for a numerical flux F(uL, uR).

    With entropy variable v = eta'(u) and potential psi = v f - q, the entropy-conservative flux is
    F* = [psi]/[v] ([.] = right minus left). The interface between states uL, uR produces entropy
    [v] F - [psi] = [v](F - F*), so the semi-discrete scheme is entropy stable (d/dt sum eta(u_i) dx
    <= boundary terms) iff Q = -[v](F - F*) >= 0 for all states. We certify Q >= 0 exactly, cell by
    cell after splitting |x| into sign cases, or find an exact rational point with Q < 0."""
    cfl = spec["claims"]["entropy_stability"].get("cfl")
    claim = ("semi-discrete entropy stability (Tadmor): Q = -(v(uR) - v(uL))*(F(uL, uR) - F*(uL, uR)) >= 0 "
             "for all uL, uR" + (f" with lam*|uL|, lam*|uR| <= {cfl}" if cfl else ""))
    assumptions = [SEMI_DISCRETE] + ([f"lam*|uL|, lam*|uR| <= {cfl} (a CFL-type bound on the states)"] if cfl else [])
    try:
        F_e = numerical_flux(spec)
        if F_e is None:
            return result("entropy_stability", NOT_APPLICABLE, claim, "no numerical flux declared")
        eta, q, how = entropy_pair(spec)
        f_e = pde_flux(spec)
        f, v = P.from_expr(f_e), P.from_expr(diff(eta, "u"))
        compat = P.add(P.from_expr(diff(q, "u")), P.mul(v, P.from_expr(diff(f_e, "u"))), -1)
        if compat:
            return result("entropy_stability", UNKNOWN, claim, f"q' - eta' f' = {P.show(compat)} != 0: not an entropy pair")
        if not P.nonneg_by_form(P.from_expr(diff(diff(eta, "u"), "u"))):
            return result("entropy_stability", UNKNOWN, claim, "eta'' >= 0 not shown by form")
        psi = P.add(P.mul(v, f), P.from_expr(q), -1)
        at = lambda p, x: P.subst(p, {"u": P.var(x)})
        jv, jpsi = (P.add(at(p, "uR"), at(p, "uL"), -1) for p in (v, psi))
        g, h = (P.divide_difference(p, "uL", "uR", 1) for p in (jv, jpsi))
        if g is None or h is None:
            return result("entropy_stability", UNKNOWN, claim, "[v] or [psi] is not divisible by uR - uL")
        Fstar = P.mul(h, P.inverse(g))
        F = P.from_expr(F_e)
        Q = P.scale(P.mul(jv, P.add(F, Fstar, -1)), -1)
        cells = sign_cells(F_e)
    except P.Undecided as ex:
        return result("entropy_stability", UNKNOWN, claim, str(ex))
    if "lam" in P.variables(Q):
        assumptions.append("lam = dt/dx > 0 is a fixed parameter of the flux")
    if any(atoms for _, atoms in cells):
        assumptions.append("|x| = sqrt(x^2) is split into the cases x >= 0 and x <= 0")
    wit = {"entropy_pair": {"eta": to_str(eta), "q": to_str(q), "source": how, "v = eta'": P.show(v),
                            "psi = v*f - q": P.show(psi), "q' - eta'*f'": "0"},
           "F_star = [psi]/[v]": P.show(Fstar), "Q": P.show(Q)}
    cons = _cfl_atoms(spec)
    D = P.divide_difference(Q, "uL", "uR", 2)
    cert = None if D is None else certify_nonneg(D, cons)
    if cert:
        wit.update({"D = Q/(uR - uL)^2": P.show(D), "certificate": cert})
        return _entropy_result(VERIFIED, claim, "Q = (uR - uL)^2 * D with D >= 0 (certificate below)", wit, assumptions)
    rows, failed = [], []
    for Fc, atoms in cells:
        Qc = P.scale(P.mul(jv, P.add(Fc, Fstar, -1)), -1)
        Dc = P.divide_difference(Qc, "uL", "uR", 2)
        target = Dc if Dc is not None else Qc
        c = certify_nonneg(target, atoms + cons)
        row = {"cell": [_show_atom(a) for a in atoms + cons], "F": P.show(Fc), "Q": P.show(Qc)}
        if Dc is not None:
            row["D = Q/(uR - uL)^2"] = P.show(Dc)
        else:
            row["certified"] = "Q itself (not divisible by (uR - uL)^2 on this cell)"
        rows.append({**row, "certificate": c or "none found"})
        if c is None:
            failed.append(len(rows) - 1)
    wit["cells"] = rows
    if not failed:
        return _entropy_result(VERIFIED, claim, f"Q >= 0 certified on each of {len(rows)} sign cells (they cover the plane)",
                               wit, assumptions)
    lams = [Fraction(1)] if "lam" not in P.variables(Q) else [Fraction(1, 2), Fraction(1), Fraction(1, 4), Fraction(2)]
    pts = [{"uL": a, "uR": b, "lam": l} for l in lams for a in _VALUES for b in _VALUES]
    pts += [{**pt, "lam": abs(pt["lam"])} for pt in _points(("uL", "uR", "lam"))]
    for pt in pts:
        if pt["lam"] == 0 or any(P.evaluate(a, pt) < 0 for a in cons):
            continue
        val = P.evaluate(Q, pt)
        if val is not None and val < 0:
            pt = {k: v for k, v in pt.items() if k != "lam" or "lam" in P.variables(Q)}
            wit["counterexample"] = {"point": _fmt(pt), "Q": str(val), "F": str(P.evaluate(F, pt)),
                                     "F_star": str(P.evaluate(Fstar, pt)),
                                     "entropy_production [v]F - [psi]": str(-val)}
            return _entropy_result(REFUTED, claim, f"Q = {val} < 0 at {_fmt(pt)}: this interface produces entropy "
                                   f"[v]F - [psi] = {-val} > 0", wit, assumptions)
    return result("entropy_stability", UNKNOWN, claim,
                  f"no certificate on sign cells {failed} and no rational point with Q < 0 found", wit, assumptions)


def _entropy_result(status, claim, detail, wit, assumptions):
    r = result("entropy_stability", status, claim, detail, wit, assumptions)
    r["guarantee"] = ENTROPY_EXACT
    return r


# ---------------------------------------------------------------- positivity (linear schemes)

def _compose_affine(c: list, lo: Fraction, w: Fraction) -> list:
    """Coefficients of p(lo + w t) from coefficients c of p(nu) (Horner)."""
    out: list = [Fraction(0)]
    for a in reversed(c):
        nxt = [Fraction(0)] * (len(out) + 1)
        for j, b in enumerate(out):
            nxt[j] += b * lo
            nxt[j + 1] += b * w
        nxt[0] += a
        out = nxt
    return out


def bernstein(c: list, lo: Fraction, hi: Fraction) -> list:
    """Bernstein coefficients of p on [lo, hi]; all >= 0 certifies p >= 0 there."""
    a = _compose_affine(c, lo, hi - lo)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    n = max(len(a) - 1, 1)
    a += [Fraction(0)] * (n + 1 - len(a))
    return [sum(Fraction(comb(k, j), comb(n, j)) * a[j] for j in range(k + 1)) for k in range(n + 1)]


def _horner(c: list, x: Fraction) -> Fraction:
    return sum((a * x ** j for j, a in enumerate(c)), Fraction(0))


class NotLinear(Exception):
    """The PDE is not u_t + a u_x = 0 or the update is not linear in (um1, u0, up1)."""


class NonlinearFlux(NotLinear):
    pass


def linear_coefficients(spec: dict) -> tuple[Fraction, dict]:
    """(a, {stencil name: c_k}) with u_i^{n+1} = sum_k c_k u_{i+k}^n for u_t + a u_x = 0, each c_k a
    Poly in nu = a*lam. Raises NotLinear (the reason) or P.Undecided."""
    f = P.from_expr(pde_flux(spec))
    H = P.from_expr(update(spec))
    if list(f) != [((("v", "u"), 1),)]:
        raise NonlinearFlux(f"nonlinear flux f = {P.show(f)}")
    a = f[((("v", "u"), 1),)]
    coeffs: dict = {}
    for m, c in H.items():
        us = [(x, k) for x, k in m if x[0] == "v" and x[1] in STENCIL]
        if len(us) != 1 or us[0][1] != 1 or any(x[0] == "s" for x, _ in m):
            raise NotLinear("update is not linear in (um1, u0, up1)")
        rest = P.subst({P._mono({x: k for x, k in m if x != us[0][0]}): c}, {"lam": P.scale(P.var("nu"), 1 / a)})
        coeffs[us[0][0][1]] = P.add(coeffs.get(us[0][0][1], {}), rest)
    return a, coeffs


def positivity(spec: dict) -> dict:
    cfl = spec.get("claims", {}).get("positive_cfl")
    if cfl is None:
        return result("positivity", NOT_APPLICABLE, "positivity", "no CFL range claimed")
    lo, hi = (Fraction(x) for x in cfl)
    claim = f"positivity: every coefficient c_k(nu) >= 0 for nu = a*dt/dx in [{lo}, {hi}]"
    try:
        a, coeffs = linear_coefficients(spec)
    except P.Undecided as ex:
        return result("positivity", UNKNOWN, claim, str(ex))
    except NonlinearFlux:
        return result("positivity", NOT_APPLICABLE, claim,
                      "nonlinear flux: positivity/monotonicity of nonlinear schemes is out of scope in v0")
    except NotLinear as ex:
        return result("positivity", NOT_APPLICABLE, claim, str(ex))
    wit: dict = {"nu": f"{a}*lam (a = {a})", "coefficients": {}, "bernstein": {}}
    for name in STENCIL:
        p = coeffs.get(name, {})
        if P.variables(p) - {"nu"} or any(k < 0 for m in p for _, k in m):
            return result("positivity", UNKNOWN, claim, f"coefficient of {name} is not a polynomial in nu")
        c = [Fraction(0)] * (1 + max((k for m in p for _, k in m), default=0))
        for m, v in p.items():
            c[m[0][1] if m else 0] += v
        b = bernstein(c, lo, hi)
        wit["coefficients"][name] = P.show(p)
        wit["bernstein"][name] = [str(x) for x in b]
        if min(b) >= 0:
            continue
        grid = [lo, hi] + [lo + (hi - lo) * Fraction(j, 64) for j in range(1, 64)]
        bad = next((x for x in grid if _horner(c, x) < 0), None)
        if bad is None:
            return result("positivity", UNKNOWN, claim, f"Bernstein test inconclusive for {name}", wit)
        wit.update(offending=name, violating_nu=str(bad), value=str(_horner(c, bad)))
        return result("positivity", REFUTED, claim,
                      f"coefficient of {name} = {P.show(p)} is {_horner(c, bad)} < 0 at nu = {bad}", wit)
    return result("positivity", VERIFIED, claim,
                  "u_i^{n+1} = sum_k c_k(nu) u_{i+k}^n with all Bernstein coefficients of each c_k on the "
                  "interval >= 0 (for affine c_k these are the endpoint values)", wit)


# ---------------------------------------------------------------- monotonicity (fully discrete, Crandall-Majda)

SCALED = {"um1": "w_m1", "u0": "w_0", "up1": "w_p1"}    # w_k = lam*u_k


def _monotone_cfl_atoms(spec: dict, c: Fraction) -> list:
    """The CFL region lam*|f'(x)| <= c for x in um1, u0, up1, as atoms c - lam*f'(x), c + lam*f'(x) >= 0.
    f' must be affine, so that for fixed lam the region is a box in (um1, u0, up1)."""
    fp = P.derivative(P.from_expr(pde_flux(spec)), "u")
    if P.variables(fp) - {"u"} or any(a[0] != "v" or k > 1 for m in fp for a, k in m):
        raise P.Undecided(f"f' = {P.show(fp)} is not affine in u, so the CFL region is not a box")
    return [P.add(P.const(c), P.mul(P.var("lam"), P.subst(fp, {"u": P.var(x)})), s) for x in STENCIL for s in (-1, 1)]


def _scaled(p: P.Poly) -> tuple[P.Poly, int]:
    """(lam^k * p with u_k = w_k/lam, k): the substitution and the factor lam^k > 0 keep the sign of p,
    and k is chosen so that no negative power of lam is left."""
    q = P.subst(p, {x: P.mul(P.var(w), P.inverse(P.var("lam"))) for x, w in SCALED.items()})
    k = -min((dict(m).get(("v", "lam"), 0) for m in q), default=0)
    return P.mul(q, P.power(P.var("lam"), k)), k


def _linear(p: P.Poly, names) -> tuple[Fraction, dict] | None:
    """(c0, {x: c}) with p = c0 + sum c*x over plain variables in names, or None if p is not affine."""
    c0, lin = Fraction(0), {}
    for m, c in p.items():
        if not m:
            c0 += c
            continue
        if len(m) != 1 or m[0][0][0] != "v" or m[0][0][1] not in names or m[0][1] != 1:
            return None
        lin[m[0][0][1]] = c
    return c0, lin


def _solve(cols: list, rhs: dict, names: list) -> list | None:
    """The unique mu with sum_j mu_j cols[j] = rhs (vectors as dicts over names), or None."""
    rows = [[col.get(v, Fraction(0)) for col in cols] + [rhs.get(v, Fraction(0))] for v in names]
    for j in range(len(cols)):
        i = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if i is None:
            return None
        rows[j], rows[i] = rows[i], rows[j]
        rows[j] = [x / rows[j][j] for x in rows[j]]
        for i2 in range(len(rows)):
            if i2 != j and rows[i2][j]:
                rows[i2] = [a - rows[i2][j] * b for a, b in zip(rows[i2], rows[j])]
    if any(row[-1] for row in rows[len(cols):]):
        return None
    return [rows[j][-1] for j in range(len(cols))]


def certify_farkas(p: P.Poly, atoms: list) -> dict | None:
    """A certificate that the affine p is >= 0 on {a >= 0 for a in atoms}: multipliers mu_j >= 0 and a
    constant r >= 0 with p - sum_j mu_j a_j = r, an identity replayed in the normal form. This is the
    affine Farkas lemma, so on a non-empty polyhedron such a certificate exists whenever p >= 0 there;
    an optimal one is basic (its atoms have independent linear parts), so trying subsets of at most
    as many atoms as there are variables is complete."""
    names = sorted(P.variables(p).union(*(P.variables(a) for a in atoms)))
    lp = _linear(p, names)
    if lp is None:
        return None
    usable = [(a, la) for a in atoms if (la := _linear(a, names)) is not None]
    for size in range(len(names) + 1):
        for combo in combinations(usable, size):
            mu = _solve([la[1] for _, la in combo], lp[1], names)
            if mu is None or any(m < 0 for m in mu):
                continue
            r = lp[0] - sum((m * la[0] for m, (_, la) in zip(mu, combo)), Fraction(0))
            rest = p
            for m, (a, _) in zip(mu, combo):
                rest = P.add(rest, P.scale(a, m), -1)
            if r < 0 or rest != P.const(r):
                continue
            return {"farkas": f"{P.show(p)} = {r}" + "".join(f" + {m}*({P.show(a)})" for m, (a, _) in zip(mu, combo) if m),
                    "multipliers": {P.show(a): str(m) for m, (a, _) in zip(mu, combo) if m}, "remainder": str(r)}
    return None


def _certify_in_lam(p: P.Poly, atoms: list) -> dict | None:
    """p(lam) >= 0 by Bernstein coefficients on the lam-interval cut out by the atoms affine in lam alone
    (a superset of the region, so this is sound)."""
    if P.variables(p) - {"lam"} or any(a[0] != "v" or k < 0 for m in p for a, k in m):
        return None
    lo, hi = Fraction(0), None
    for a in atoms:
        la = _linear(a, ["lam"])
        if la is None or not la[1]:
            continue
        b = -la[0] / la[1]["lam"]
        if la[1]["lam"] > 0:
            lo = max(lo, b)
        else:
            hi = b if hi is None else min(hi, b)
    if hi is None or hi < lo:
        return None
    c = [Fraction(0)] * (1 + max((k for m in p for _, k in m), default=0))
    for m, v in p.items():
        c[m[0][1] if m else 0] += v
    b = bernstein(c, lo, hi)
    return {"bernstein_on_lam": [str(lo), str(hi)], "coefficients": [str(x) for x in b]} if min(b) >= 0 else None


def _certify_partial(p: P.Poly, atoms: list) -> dict | None:
    """certify_nonneg (by form; its change of variables is for uL, uR only and finds nothing here), then
    the affine Farkas certificate, then Bernstein in lam. Each is a sufficient condition for p >= 0."""
    return certify_nonneg(p, atoms) or certify_farkas(p, atoms) or _certify_in_lam(p, atoms)


def _box(atoms: list, lam: Fraction, x: str) -> tuple[Fraction, Fraction] | None:
    """The interval of x allowed by the CFL atoms at this lam ([-1, 1] if they do not bound x)."""
    lo, hi = None, None
    for a in atoms:
        la = _linear(P.subst(a, {"lam": P.const(lam)}), [x])
        if la is None:
            return None
        if not la[1]:
            if la[0] < 0:
                return None
            continue
        b = -la[0] / la[1][x]
        if la[1][x] > 0:
            lo = b if lo is None else max(lo, b)
        else:
            hi = b if hi is None else min(hi, b)
    lo, hi = (Fraction(-1) if lo is None else lo), (Fraction(1) if hi is None else hi)
    return (lo, hi) if lo < hi else None


def _vertices(atoms: list, names: list) -> list[dict]:
    """The vertices of the polytope {a >= 0 for a in atoms} (all affine in names), exactly."""
    lins = [_linear(a, names) for a in atoms]
    if None in lins:
        return []
    out = []
    for combo in combinations(range(len(lins)), len(names)):
        cols = [{i: lins[i][1].get(v, Fraction(0)) for i in combo} for v in names]
        x = _solve(cols, {i: -lins[i][0] for i in combo}, list(combo))
        if x is None:
            continue
        pt = dict(zip(names, x))
        if pt not in out and all(c0 + sum(c * pt[v] for v, c in lin.items()) >= 0 for c0, lin in lins):
            out.append(pt)
    return out


def _probe_cell(H: P.Poly, p: P.Poly, reg: list, cfl: list, x: str) -> dict | None:
    """Guided search on a cell where the scaled partial p (in w) was not certified: at lam = 1 (so
    w = u), take the vertex of the cell where p is least and step towards the centroid, so the state
    is inside the cell, then look for an exact decreasing pair."""
    one = {"lam": P.const(1)}
    p1, reg1 = P.subst(p, one), [P.subst(a, one) for a in reg]
    names = sorted(SCALED.values())
    if P.variables(p1) - set(names):
        return None
    vs = _vertices(reg1, names)
    if not vs or _linear(p1, names) is None:
        return None
    val = lambda pt: P.evaluate(p1, pt)
    v = min(vs, key=val)
    if val(v) >= 0:
        return None
    g = {n: sum(pt[n] for pt in vs) / len(vs) for n in names}
    box = _box([a for a in cfl if x in P.variables(a)], Fraction(1), x)
    for eps in (Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)):
        s = {u: v[w] + eps * (g[w] - v[w]) for u, w in SCALED.items()}
        s["lam"] = Fraction(1)
        h0 = P.evaluate(H, s)
        for h in (eps / 10, eps / 100):
            if h0 is None or box is None or s[x] + h > box[1]:
                continue
            h1 = P.evaluate(H, {**s, x: s[x] + h})
            if h1 is not None and h1 < h0:
                return {"lam": "1", "state (um1, u0, up1)": [str(s[k]) for k in STENCIL],
                        "increased": x, "by": str(h), "H before": str(h0), "H after": str(h1)}
    return None


def _decrease(H: P.Poly, cfl: list) -> dict | None:
    """Exact states s <= s' (differing in one argument) in the CFL region with H(s') < H(s), or None."""
    lams = [Fraction(1), Fraction(1, 2), Fraction(2), Fraction(1, 3)]
    if not any(P.variables(a) & set(STENCIL) for a in cfl):           # f' constant: the CFL bounds lam
        hi = min((-la[0] / la[1]["lam"] for a in cfl if (la := _linear(a, ["lam"])) and la[1].get("lam", 0) < 0),
                 default=Fraction(1))
        lams = [hi * Fraction(t) for t in (1, "99/100", "3/4", "1/2", "1/4", "1/10")]
    ts = [Fraction(t) for t in (0, "1/6", "1/4", "1/3", "1/2", "2/3", "3/4", "5/6", 1)]
    for lam in lams:
        box = {x: _box([a for a in cfl if x in P.variables(a) or not P.variables(a) & set(STENCIL)], lam, x)
               for x in STENCIL}
        if None in box.values():
            continue
        vals = {x: [lo + (hi - lo) * t for t in ts] for x, (lo, hi) in box.items()}
        for um1 in vals["um1"]:
            for u0 in vals["u0"]:
                for up1 in vals["up1"]:
                    s = {"um1": um1, "u0": u0, "up1": up1, "lam": lam}
                    h0 = P.evaluate(H, s)
                    for x in STENCIL:
                        lo, hi = box[x]
                        h = (hi - lo) / 120
                        if h0 is None or s[x] + h > hi:
                            continue
                        h1 = P.evaluate(H, {**s, x: s[x] + h})
                        if h1 is not None and h1 < h0:
                            return {"lam": str(lam), "state (um1, u0, up1)": [str(s[k]) for k in STENCIL],
                                    "increased": x, "by": str(h), "H before": str(h0), "H after": str(h1)}
    return None


def monotonicity(spec: dict) -> dict:
    """Monotonicity of the fully discrete update u_i^{n+1} = H(u_{i-1}, u_i, u_{i+1}) under a CFL bound.

    The claim: H is non-decreasing in each argument for lam = dt/dx > 0 and states with
    lam*|f'(u)| <= c (c = claims.monotone_cfl), f' affine, so that for fixed lam the region is a box.

    Method. Every |x| = sqrt(x^2) in H is split into sign cases (`sign_cells`); on each closed cell
    H equals a polynomial H_c. We differentiate H_c in um1, u0 and up1 and certify each partial >= 0
    on the cell intersected with the CFL region. To make the certificates affine we substitute
    u_k = w_k/lam and multiply by a power of lam (both keep signs, as lam > 0); then each partial and
    each atom is affine in (w_m1, w_0, w_p1, lam) for the three-point Burgers and advection fluxes.
    Certificates: by form (`certify_nonneg`), an affine Farkas identity p = r + sum mu_j a_j with
    mu_j, r >= 0, or Bernstein coefficients in lam. A cell whose atoms are contradictory (a Farkas
    certificate that -1 >= 0 on it) is empty and skipped.

    Why non-negative partials on every cell imply H is non-decreasing, boundaries included: H is
    built from polynomials and |.|, so it is continuous and locally Lipschitz. Fix lam and two
    arguments and let g(t) = H with the third argument t, on an interval of the box. The closed
    cells cover it, and each meets the line in finitely many closed intervals and points (the cells
    are semi-algebraic). Away from the finitely many endpoints, t is interior to some cell's piece,
    where g' = dH_c/dt >= 0. g is Lipschitz, so g(b) - g(a) is the integral of g', which is >= 0: a
    finite set of kinks has measure zero, and a one-sided derivative there is never needed.

    REFUTED needs exact rational states s <= s', differing in one argument, both in the CFL region,
    with H(s') < H(s) in Fraction arithmetic: a direct violation of the claim, not of a derivative."""
    c = spec.get("claims", {}).get("monotone_cfl")
    claim = (f"monotone: H(um1, u0, up1) is non-decreasing in each argument for lam > 0 and states with "
             f"lam*|f'(u)| <= {c}")
    if c is None:
        return result("monotonicity", NOT_APPLICABLE, "monotonicity", "no CFL bound claimed (claims.monotone_cfl)")
    assumptions = ["lam = dt/dx > 0", f"every state u in the stencil has lam*|f'(u)| <= {c}"]
    try:
        e = update(spec)
        H = P.from_expr(e)
        cfl = _monotone_cfl_atoms(spec, Fraction(c))
        region = [_scaled(a)[0] for a in cfl] + [P.var("lam")]
        cells = sign_cells(e)
        rows, failed, probes = [], [], []
        for Hc, atoms in cells:
            reg = [_scaled(a)[0] for a in atoms] + region
            row = {"cell": [_show_atom(a) for a in atoms], "H": P.show(Hc), "partials": {}}
            bad = []
            for x in STENCIL:
                d = P.derivative(Hc, x)
                s, k = _scaled(d)
                cert = _certify_partial(s, reg)
                row["partials"][x] = {f"dH/d{x}": P.show(d), f"lam^{k}*dH/d{x} in w": P.show(s),
                                      "certificate": cert or "none found"}
                if cert is None:
                    bad.append(x)
                    probes.append((s, reg, x))
            if bad and (empty := certify_farkas(P.const(-1), reg)):
                row["empty"], bad = empty, []
            failed += [(len(rows), x) for x in bad]
            rows.append(row)
    except P.Undecided as ex:
        return result("monotonicity", UNKNOWN, claim, str(ex), assumptions=assumptions)
    wit = {"H": P.show(H), "region": [_show_atom(a) for a in cfl] + ["lam > 0"],
           "scaling": "w_m1 = lam*um1, w_0 = lam*u0, w_p1 = lam*up1", "cells": rows}
    if any(atoms for _, atoms in cells):
        assumptions.append("|x| = sqrt(x^2) is split into the cases x >= 0 and x <= 0")
    if not failed:
        return result("monotonicity", VERIFIED, claim,
                      f"every partial of H is >= 0 on each of {len(rows)} closed sign cells within the CFL region "
                      "(certificates below); H is continuous, so it is non-decreasing", wit, assumptions)
    hit = next((h for s, reg, x in probes if (h := _probe_cell(H, s, reg, cfl, x))), None) or _decrease(H, cfl)
    if hit:
        wit["counterexample"] = hit
        return result("monotonicity", REFUTED, claim,
                      f"H decreases from {hit['H before']} to {hit['H after']} when {hit['increased']} increases by "
                      f"{hit['by']} at lam = {hit['lam']}, state {hit['state (um1, u0, up1)']}", wit, assumptions)
    return result("monotonicity", UNKNOWN, claim,
                  f"no certificate for {failed} and no decreasing pair of rational states found", wit, assumptions)
