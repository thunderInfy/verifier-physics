"""Exact structural checks for 1D three-point schemes u_t + f(u)_x = 0.

Stencil variables: um1, u0, up1 (u_{i-1}^n, u_i^n, u_{i+1}^n) and lam = dt/dx. A numerical
flux F is written in uL, uR. Every check returns a plain dict with an explicit witness
(a normal form, a recovered flux, a coefficient list, or an exact rational counterexample),
so each verdict can later be replayed as a Lean certificate.

Statuses: VERIFIED (exact identity or exact inequality certificate), REFUTED (exact rational
counterexample, re-evaluated in Fraction arithmetic), UNKNOWN (outside the decided fragment),
NOT_APPLICABLE. No verdict here ever rests on a floating-point number.
"""

from __future__ import annotations

import random
from fractions import Fraction
from math import comb

from ..expr import E, lit, parse, substitute, var
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
