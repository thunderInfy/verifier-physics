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


def positivity(spec: dict) -> dict:
    cfl = spec.get("claims", {}).get("positive_cfl")
    if cfl is None:
        return result("positivity", NOT_APPLICABLE, "positivity", "no CFL range claimed")
    lo, hi = (Fraction(x) for x in cfl)
    claim = f"positivity: every coefficient c_k(nu) >= 0 for nu = a*dt/dx in [{lo}, {hi}]"
    try:
        f = P.from_expr(pde_flux(spec))
        H = P.from_expr(update(spec))
    except P.Undecided as ex:
        return result("positivity", UNKNOWN, claim, str(ex))
    if list(f) != [((("v", "u"), 1),)]:
        return result("positivity", NOT_APPLICABLE, claim,
                      "nonlinear flux: positivity/monotonicity of nonlinear schemes is out of scope in v0")
    a = f[((("v", "u"), 1),)]
    coeffs: dict = {}
    for m, c in H.items():
        us = [(x, k) for x, k in m if x[0] == "v" and x[1] in STENCIL]
        if len(us) != 1 or us[0][1] != 1 or any(x[0] == "s" for x, _ in m):
            return result("positivity", NOT_APPLICABLE, claim, "update is not linear in (um1, u0, up1)")
        rest = P.subst({P._mono({x: k for x, k in m if x != us[0][0]}): c}, {"lam": P.scale(P.var("nu"), 1 / a)})
        coeffs[us[0][0][1]] = P.add(coeffs.get(us[0][0][1], {}), rest)
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
