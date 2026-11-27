"""Checks for 1D systems q_t + f(q)_x = 0 with n components (n = 1 is the scalar case).

Spec format (plain dicts, as for scalar specs):

    "pde": {"state": ["h", "m"], "flux": ["m", "m^2/h + g*h^2/2"],
            "parameters": {"g": "positive"}, "domain": {"h": "positive"}}
    "scheme": {"numerical_flux": [F_1, ..., F_n]}   in hL, hR, mL, mR, lam and the parameters
          or  {"update": [H_1, ..., H_n]}           in hm1, h0, hp1, mm1, m0, mp1, lam, ...

Component c on the stencil is cm1, c0, cp1 (c_{i-1}^n, c_i^n, c_{i+1}^n) and cL, cR in a
numerical flux, so a scalar spec, read with state ["u"], is the 1-component case. The only domain
constraint is "positive" (> 0); a parameter keeps its symbol in the exact checks.

Exact checks (Fraction arithmetic, as in checks.py; every result holds on the stated domain and
says so in its assumptions):
- hyperbolicity: the flux Jacobian A(q) symbolically, and for n = 2 the discriminant
  tr(A)^2 - 4 det(A) > 0, which is equivalent to real distinct eigenvalues of a real 2x2 matrix;
- conservation: componentwise telescoping, as in checks.telescoping, from a base point inside
  the domain (h = 1 rather than h = 0, which is not in it);
- consistency: F_k(q, q) = f_k(q) for each component.

Empirical studies (numpy floats): Riemann problems for shallow water on [0, 1] with transmissive
boundaries, against the exact Riemann solution, giving the depth-positivity and L1-convergence
checks. Shallow water only (the exact solver below is for f = (m, m^2/h + g h^2/2)).
"""

from __future__ import annotations

import math
import random
from fractions import Fraction
from itertools import product

import numpy as np

from ..expr import E, lit, parse, substitute, var, variables as expr_variables
from . import checks, poly as P
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result
from .convergence import EMPIRICAL, NOT_REFUTED, REFUTED_EMPIRICALLY, _steps, evaluator

SLOTS = ("m1", "0", "p1")


def is_system(spec: dict) -> bool:
    return isinstance(spec["pde"]["flux"], list)


def _domain(d: dict) -> set[str]:
    bad = {k: v for k, v in d.items() if v != "positive"}
    if bad:
        raise ValueError(f"unsupported domain constraints {bad}; only \"positive\" (> 0) is supported")
    return set(d)


def read(spec: dict) -> dict:
    """{state, flux, nf, update, positive, params} for a system spec or a scalar one (state ["u"])."""
    pde, sch = spec["pde"], spec["scheme"]
    many = is_system(spec)
    state = pde["state"] if many else ["u"]
    listed = lambda x: x if many or x is None else [x]
    ex = lambda s: checks._expr(spec, s)
    flux = [ex(s) for s in listed(pde["flux"])]
    nf = listed(sch.get("numerical_flux"))
    nf = None if nf is None else [ex(s) for s in nf]
    if len(flux) != len(state) or (nf is not None and len(nf) != len(state)):
        raise ValueError("state, flux and numerical flux must have the same number of components")
    if nf is not None:
        def at(F, l, r):
            return substitute(F, {f"{c}{s}": var(f"{c}{t}") for c in state for s, t in (("L", l), ("R", r))})
        update = [E("sub", (var(f"{c}0"), E("mul", (var("lam"), E("sub", (at(F, "0", "p1"), at(F, "m1", "0")))))))
                  for c, F in zip(state, nf)]
    else:
        update = [ex(s) for s in listed(sch["update"])]
    params, dom = _domain(pde.get("parameters", {})), _domain(pde.get("domain", {}))
    # every cell's state is in the domain, so its stencil and interface copies are positive as well
    copies = {f"{c}{s}" for c in dom for s in ("", "L", "R") + SLOTS}
    return {"state": state, "flux": flux, "nf": nf, "update": update, "params": params, "domain": dom,
            "positive": params | copies}


def _assumptions(sys: dict) -> list[str]:
    pos = sorted(sys["params"] | sys["domain"])
    return [f"on the stated domain {', '.join(x + ' > 0' for x in pos)}, in every cell (denominators are "
            "monomials, and square-root arguments non-negative by form, in these variables)"] if pos else []


def _norm(sys: dict, e: E) -> P.Poly:
    return P.from_expr(e, positive=sys["positive"])


def _points(names, positive, n=200, seed=0):
    """Exact rational points, positive where the domain says so."""
    rng = random.Random(seed)
    yield {v: Fraction(1) for v in names}
    for _ in range(n):
        yield {v: Fraction((1 if v in positive else rng.choice([1, -1])) * rng.randint(1, 9), rng.randint(1, 4))
               for v in names}


def _base(sys: dict) -> dict:
    """A point in the state domain: 1 for positive components, 0 otherwise."""
    return {c: P.const(1 if c in sys["positive"] else 0) for c in sys["state"]}


# ---------------------------------------------------------------- hyperbolicity

def jacobian(sys: dict) -> list[list[P.Poly]]:
    f = [_norm(sys, e) for e in sys["flux"]]
    return [[P.derivative(fi, c) for c in sys["state"]] for fi in f]


def hyperbolicity(spec: dict) -> dict:
    """Strict hyperbolicity on the stated domain: A(q) = df/dq has n real, distinct eigenvalues for
    every state and parameter in it. For n = 2, with t = tr A and d = det A, the eigenvalues are
    (t +- sqrt(t^2 - 4d))/2, so they are real and distinct iff the discriminant t^2 - 4d > 0: the
    check is equivalent to the claim. VERIFIED when the discriminant is > 0 by form with the domain
    variables positive (P.positive_by_form); REFUTED at an exact rational domain point where it is
    <= 0 (repeated or complex eigenvalues there). For n > 2 the check is UNKNOWN: tr^2 - 4 det is
    the 2x2 discriminant only; a cubic's discriminant would still decide n = 3, but from n = 4 on a
    positive discriminant also allows two complex pairs, so a Sturm-type root count would be needed.
    Neither is implemented."""
    claim = "strictly hyperbolic on the stated domain: df/dq has real, distinct eigenvalues"
    try:
        sys = read(spec)
        A = jacobian(sys)
    except P.Undecided as ex:
        return result("hyperbolicity", UNKNOWN, claim, str(ex))
    n, assumptions = len(sys["state"]), _assumptions(sys)
    wit = {"A = df/dq": [[P.show(x) for x in row] for row in A]}
    if n == 1:
        return result("hyperbolicity", VERIFIED, claim, "one component: the 1x1 Jacobian f'(u) is real", wit,
                      assumptions)
    if n > 2:
        return result("hyperbolicity", UNKNOWN, claim, f"{n} components: the discriminant test is for 2x2 "
                      "systems only and does not generalise", wit, assumptions)
    (a, b), (c, d) = A
    tr, det = P.add(a, d), P.add(P.mul(a, d), P.mul(b, c), -1)
    disc = P.add(P.mul(tr, tr), P.scale(det, 4), -1)
    wit.update({"tr A": P.show(tr), "det A": P.show(det), "discriminant tr^2 - 4 det": P.show(disc),
                "eigenvalues (information only)": f"({P.show(tr)})/2 +- sqrt({P.show(P.scale(disc, Fraction(1, 4)))})"})
    if P.positive_by_form(disc, positive=sys["positive"]):
        return result("hyperbolicity", VERIFIED, claim,
                      f"discriminant {P.show(disc)} > 0 by form (positive coefficients, domain variables positive, "
                      "other variables to even powers, one monomial in domain variables only)", wit, assumptions)
    for pt in _points(sorted(P.variables(disc)), sys["positive"]):
        v = P.evaluate(disc, pt)
        if v is not None and v <= 0:
            wit.update(point=checks._fmt(pt), discriminant_value=str(v))
            kind = "a repeated eigenvalue" if v == 0 else "complex eigenvalues (elliptic there)"
            return result("hyperbolicity", REFUTED, claim, f"discriminant = {v} <= 0 at {checks._fmt(pt)}: {kind}",
                          wit, assumptions)
    return result("hyperbolicity", UNKNOWN, claim, f"discriminant {P.show(disc)}: no positivity certificate by form "
                  "and no domain point with discriminant <= 0 found", wit, assumptions)


# ---------------------------------------------------------------- conservation

def telescoping(H: P.Poly, c: str, sys: dict) -> tuple[P.Poly, P.Poly]:
    """checks.telescoping for component c of a system: Phi(X, Y) with H - c0 = Phi(q0, qp1) - Phi(qm1, q0),
    X, Y vectors of fresh variables _x_k, _y_k. With D = H - c0 and a base state q* in the domain,
    D(q*, X, Y) + D(q*, q*, X) = Phi(X, Y) - Phi(q*, q*) whenever such a Phi exists, so this candidate is
    the only one up to a constant; the update is in flux form iff the residual normal form is 0."""
    D = P.add(H, P.var(f"{c}0"), -1)
    base, st = _base(sys), sys["state"]
    X, Y = ({k: P.var(f"_{s}_{k}") for k in st} for s in "xy")
    sub = lambda a, b, d: {f"{k}{s}": v[k] for k in st for s, v in zip(SLOTS, (a, b, d))}
    phi = P.add(P.subst(D, sub(base, X, Y)), P.subst(D, sub(base, base, X)))
    at = lambda l, r: P.subst(phi, {**{f"_x_{k}": P.var(f"{k}{l}") for k in st},
                                   **{f"_y_{k}": P.var(f"{k}{r}") for k in st}})
    return phi, P.add(D, P.add(at("0", "p1"), at("m1", "0"), -1), -1)


def _periodic_change(Hs: list, sys: dict, state: list[dict], env: dict) -> list | None:
    """sum_i (q_i^{n+1} - q_i^n) per component on a periodic grid, exactly (None if irrational)."""
    n, out = len(state), []
    for H, c in zip(Hs, sys["state"]):
        total = Fraction(0)
        for i in range(n):
            pt = {**env, **{f"{k}{s}": state[j % n][k] for k in sys["state"] for s, j in zip(SLOTS, (i - 1, i, i + 1))}}
            v = P.evaluate(H, pt)
            if v is None:
                return None
            total += v - state[i][c]
        out.append(total)
    return out


def _flux_from_phi(phi: P.Poly, sys: dict, f: P.Poly) -> P.Poly:
    """-Phi(qL, qR)/lam, the numerical flux, with its free constant fixed by F(q*, q*) = f(q*) at the
    base state q* (any constant gives the same update)."""
    F = P.subst(phi, {f"_{s}_{k}": P.var(f"{k}{t}") for k in sys["state"] for s, t in (("x", "L"), ("y", "R"))})
    F = P.scale(P.mul(F, P.inverse(P.var("lam"))), -1)
    base = _base(sys)
    return P.add(F, P.add(P.subst(f, base), P.subst(F, {f"{k}{s}": base[k] for k in sys["state"] for s in "LR"}), -1))


def conservation(spec: dict) -> dict:
    claim = "discrete conservation of every component on a periodic grid: sum_i (q_i^{n+1} - q_i^n) = 0"
    try:
        sys = read(spec)
        Hs = [_norm(sys, h) for h in sys["update"]]
        tel = [telescoping(H, c, sys) for H, c in zip(Hs, sys["state"])]
    except P.Undecided as ex:
        return result("conservation", UNKNOWN, claim, str(ex))
    assumptions = ["lam = dt/dx != 0"] + _assumptions(sys)
    res = {c: P.show(r) for c, (_, r) in zip(sys["state"], tel)}
    if not any(r for _, r in tel):
        return result("conservation", VERIFIED, claim, "every component telescopes: q_i^{n+1} - q_i^n = "
                      "-lam*(F(q_i, q_{i+1}) - F(q_{i-1}, q_i))",
                      {"recovered_flux": {c: P.show(_flux_from_phi(phi, sys, _norm(sys, f)))
                                          for c, (phi, _), f in zip(sys["state"], tel, sys["flux"])},
                       "residual_normal_form": res}, assumptions)
    rng = random.Random(2)
    names = sorted(sys["params"])
    for n in (3, 4, 5, 6):
        for _ in range(50):
            state = [{c: Fraction((1 if c in sys["positive"] else rng.choice([1, -1])) * rng.randint(1, 9),
                                  rng.randint(1, 3)) for c in sys["state"]} for _ in range(n)]
            env = {"lam": Fraction(rng.randint(1, 4), rng.randint(1, 4)),
                   **{p: Fraction(rng.randint(1, 9), rng.randint(1, 3)) for p in names}}
            d = _periodic_change(Hs, sys, state, env)
            if d and any(d):
                bad = [c for c, x in zip(sys["state"], d) if x]
                return result("conservation", REFUTED, claim,
                              f"component {', '.join(bad)} is not in flux form; its total changes by "
                              f"{', '.join(str(x) for x in d if x)} on the periodic state below",
                              {"telescoping_residual": res,
                               "state": [{c: str(v) for c, v in s.items()} for s in state],
                               **{k: str(v) for k, v in env.items()},
                               "sum_change": {c: str(x) for c, x in zip(sys["state"], d)}}, assumptions)
    return result("conservation", UNKNOWN, claim, f"telescoping residuals {res} are not all zero, but no "
                  "counterexample found", {"telescoping_residual": res}, assumptions)


# ---------------------------------------------------------------- consistency

def consistency(spec: dict) -> dict:
    claim = "consistency: F_k(q, q) = f_k(q) for every component"
    try:
        sys = read(spec)
        st = sys["state"]
        f = [_norm(sys, e) for e in sys["flux"]]
        if sys["nf"] is not None:
            F, how = [_norm(sys, e) for e in sys["nf"]], "declared numerical flux"
        else:
            Hs = [_norm(sys, h) for h in sys["update"]]
            tel = [telescoping(H, c, sys) for H, c in zip(Hs, st)]
            if any(r for _, r in tel):
                return result("consistency", NOT_APPLICABLE, claim, "update is not in flux form, so it has no numerical flux")
            F = [_flux_from_phi(phi, sys, fk) for (phi, _), fk in zip(tel, f)]
            how = "flux recovered from the update (fixed up to a constant by F(q*, q*) = f(q*) at a base state q*)"
        same = {f"{k}{s}": P.var(k) for k in st for s in "LR"}
        Fqq = [P.subst(Fk, same) for Fk in F]
        r = [P.add(a, b, -1) for a, b in zip(Fqq, f)]
    except P.Undecided as ex:
        return result("consistency", UNKNOWN, claim, str(ex))
    sq = any("sqrt" in P.show(x) for x in F)
    assumptions = _assumptions(sys) + (["square roots are real on the stated domain, so sqrt(p)^2 = p"] if sq else [])
    wit = {"F(q,q)": {c: P.show(x) for c, x in zip(st, Fqq)}, "f(q)": {c: P.show(x) for c, x in zip(st, f)},
           "residual_normal_form": {c: P.show(x) for c, x in zip(st, r)}, "flux": how}
    if not any(r):
        return result("consistency", VERIFIED, claim, "F_k(q,q) - f_k(q) normalizes to 0 for every component", wit,
                      assumptions)
    for c, rk in zip(st, r):
        if not rk:
            continue
        for pt in _points(sorted(P.variables(rk)), sys["positive"]):
            v = P.evaluate(rk, pt)
            if v:
                wit.update(component=c, point=checks._fmt(pt), residual_value=str(v))
                return result("consistency", REFUTED, claim, f"F_{c}(q,q) - f_{c}(q) = {v} at {checks._fmt(pt)}", wit,
                              assumptions)
    return result("consistency", UNKNOWN, claim, "non-zero residual not decided", wit, assumptions)


# ---------------------------------------------------------------- exact Riemann solver (shallow water)

def _f_side(h, hK, g):
    """Toro's f_K: the velocity jump across the K-wave to depth h (rarefaction if h <= hK, else shock)."""
    if h <= hK:
        return 2 * (math.sqrt(g * h) - math.sqrt(g * hK))
    return (h - hK) * math.sqrt(g / 2 * (h + hK) / (h * hK))


def star_state(hL, uL, hR, uR, g) -> tuple[float, float]:
    """(h*, u*) between the two waves, by bisection on the increasing f_L(h) + f_R(h) + uR - uL."""
    cL, cR = math.sqrt(g * hL), math.sqrt(g * hR)
    if 2 * (cL + cR) <= uR - uL:
        raise ValueError("the data create a dry bed (vacuum); not handled")
    phi = lambda h: _f_side(h, hL, g) + _f_side(h, hR, g) + uR - uL
    lo, hi = 0.0, max(hL, hR)
    while phi(hi) < 0:
        hi *= 2
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if phi(mid) < 0 else (lo, mid)
    h = (lo + hi) / 2
    return h, (uL + uR) / 2 + (_f_side(h, hR, g) - _f_side(h, hL, g)) / 2


def riemann_exact(xi: np.ndarray, hL, uL, hR, uR, g) -> tuple[np.ndarray, np.ndarray]:
    """(h, u) of the exact self-similar solution at xi = (x - x0)/t: a rarefaction or a shock on each
    side of the star state (Toro, Shock-Capturing Methods for Free-Surface Shallow Flows, ch. 5)."""
    hs, us = star_state(hL, uL, hR, uR, g)
    cL, cR, cs = math.sqrt(g * hL), math.sqrt(g * hR), math.sqrt(g * hs)
    h, u = np.empty_like(xi), np.empty_like(xi)
    left = xi <= us
    if hs > hL:                                   # left shock
        s = uL - cL * math.sqrt((hs + hL) * hs / (2 * hL * hL))
        l_out = xi < s
        fan = np.zeros_like(xi, dtype=bool)
    else:                                         # left rarefaction: head uL - cL, tail u* - c*
        l_out, fan = xi < uL - cL, (xi >= uL - cL) & (xi < us - cs)
    h[left], u[left] = hs, us
    h[left & l_out], u[left & l_out] = hL, uL
    m = left & fan
    c = (uL + 2 * cL - xi[m]) / 3
    h[m], u[m] = c * c / g, (uL + 2 * cL + 2 * xi[m]) / 3
    right = ~left
    if hs > hR:                                   # right shock
        s = uR + cR * math.sqrt((hs + hR) * hs / (2 * hR * hR))
        r_out = xi > s
        fan = np.zeros_like(xi, dtype=bool)
    else:                                         # right rarefaction: tail u* + c*, head uR + cR
        r_out, fan = xi > uR + cR, (xi > us + cs) & (xi <= uR + cR)
    h[right], u[right] = hs, us
    h[right & r_out], u[right & r_out] = hR, uR
    m = right & fan
    c = (-uR + 2 * cR + xi[m]) / 3
    h[m], u[m] = c * c / g, (uR - 2 * cR + 2 * xi[m]) / 3
    return h, u


def wave_speeds(hL, uL, hR, uR, g) -> tuple[float, float]:
    """(slowest, fastest) speed of the exact solution's outer waves (rarefaction heads or shocks)."""
    hs, _ = star_state(hL, uL, hR, uR, g)
    cL, cR = math.sqrt(g * hL), math.sqrt(g * hR)
    lo = uL - cL * math.sqrt((hs + hL) * hs / (2 * hL * hL)) if hs > hL else uL - cL
    hi = uR + cR * math.sqrt((hs + hR) * hs / (2 * hR * hR)) if hs > hR else uR + cR
    return lo, hi


def cell_averages(n: int, T: float, x0: float, case: tuple, g: float, sub: int = 16):
    """Exact cell averages of h and m = h u at time T, by the midpoint rule on `sub` points per cell."""
    x = (np.arange(n)[:, None] + (np.arange(sub)[None, :] + 0.5) / sub) / n
    h, u = riemann_exact((x.ravel() - x0) / T, *case, g)
    return h.reshape(n, sub).mean(axis=1), (h * u).reshape(n, sub).mean(axis=1)


# ---------------------------------------------------------------- Riemann studies (depth positivity, L1 error)

ORDER = 0.3
GRIDS = (100, 200, 400, 800)
LAMS = ("2/5", "37/100")
SW_FLUX = ("m", "m^2/h + g*h^2/2")
LABEL = ("shallow-water Riemann problem on [0, 1], jump at the cell interface x0, transmissive "
         "(constant-extrapolation) boundaries; L1 error at T of (h, m) against exact cell averages of the "
         "exact Riemann solution (rarefaction or shock on each side)")


def _shallow_water(spec: dict) -> bool:
    pde = spec["pde"]
    if pde.get("state") != ["h", "m"] or "g" not in pde.get("parameters", {}):
        return False
    return all(not P.add(P.from_expr(parse(a)), P.from_expr(parse(b)), -1) for a, b in zip(pde["flux"], SW_FLUX))


def run(Hs: list, case: tuple, g: float, x0: float, T: float, lam: float, n: int) -> dict:
    hL, uL, hR, uR = case
    fs, dx = [evaluator(H) for H in Hs], 1 / n
    assert abs(x0 * n - round(x0 * n)) < 1e-9, "x0 must be a cell interface"
    x = (np.arange(n) + 0.5) * dx
    h, m = np.where(x < x0, hL, hR), np.where(x < x0, hL * uL, hR * uR)
    steps, dt = _steps(T, lam * dx)
    min_h, cfl, bad_step = float(np.min(h)), 0.0, None
    with np.errstate(all="ignore"):
        for k in range(steps):
            cfl = max(cfl, float(np.max(np.abs(m / h) + np.sqrt(g * h))) * dt / dx)
            sh = lambda a: (np.concatenate(([a[0]], a[:-1])), a, np.concatenate((a[1:], [a[-1]])))
            env = {"lam": dt / dx, **dict(zip(("hm1", "h0", "hp1"), sh(h))), **dict(zip(("mm1", "m0", "mp1"), sh(m)))}
            h, m = [np.broadcast_to(f(env), h.shape).astype(float) for f in fs]
            low = float(np.min(h)) if np.all(np.isfinite(h)) else float("nan")
            min_h = min(min_h, low) if math.isfinite(low) else low
            if not low > 0:
                bad_step = k + 1
                break
    finite = bool(np.all(np.isfinite(h)) and np.all(np.isfinite(m)))
    out = {"N": n, "min_h": min_h, "cfl": cfl, "bad_step": bad_step, "finite": finite,
           "ends": (float(h[0]), float(m[0]), float(h[-1]), float(m[-1]))}
    if bad_step is None and finite:
        he, me = cell_averages(n, T, x0, case, g)
        out["L1_h"], out["L1_m"] = float(np.sum(np.abs(h - he)) * dx), float(np.sum(np.abs(m - me)) * dx)
    else:
        out["L1_h"] = out["L1_m"] = float("nan")
    out["L1"] = out["L1_h"] + out["L1_m"]
    return out


def _l1_verdict(rows: list) -> tuple[str, str]:
    a, b = rows[-2:]
    e1, e2 = a["L1"], b["L1"]
    if not (math.isfinite(e1) and math.isfinite(e2)) or e1 <= 0 or e2 <= 0:
        return UNKNOWN, "error vanished or is not finite"
    p = math.log(e1 / e2) / math.log(b["N"] / a["N"])
    msg = f"L1 error of (h, m) {e1:.3e} at N = {a['N']}, {e2:.3e} at N = {b['N']} (observed order {p:.2f})"
    if p >= ORDER:
        return NOT_REFUTED, msg
    if abs(e2 - e1) < 0.1 * e2:
        return REFUTED_EMPIRICALLY, msg + " (settled at a non-zero value: the limit is not the exact solution)"
    return UNKNOWN, msg + " (inconclusive)"


def riemann_studies(spec: dict, grids=GRIDS) -> list[dict]:
    """Two empirical checks from one set of runs: depth_positivity (min h > 0 at every step, on every
    grid and dt/dx, with the observed CFL number at most the claimed one) and riemann_l1 (the L1 error
    against the exact solution falls at observed order >= ORDER on the last two grids). Each case runs
    at every dt/dx in `lams` (default 2/5 and 37/100: one deliberately incommensurate, so that a
    result tied to a lucky ratio of dt to dx does not pass)."""
    c = spec["claims"]["riemann"]
    g, x0 = Fraction(c["g"]), Fraction(c.get("x0", "1/2"))
    lams, cfl = [Fraction(v) for v in c.get("lams", LAMS)], Fraction(c["cfl"])
    cases = c["cases"]
    data = lambda k: tuple(float(Fraction(k[v])) for v in ("hL", "uL", "hR", "uR"))
    desc = ", ".join(f"{k.get('name', 'case')} (hL, uL, hR, uR) = ({k['hL']}, {k['uL']}, {k['hR']}, {k['uR']})"
                     for k in cases)
    pos_claim = f"depth stays positive, min h > 0, at observed CFL number lam*max(|u| + sqrt(g h)) <= {cfl} on {desc}"
    l1_claim = f"converges in L1 to the exact Riemann solution on {desc}"
    if not _shallow_water(spec):
        why = "the exact Riemann solver is for shallow water f = (m, m^2/h + g h^2/2) only"
        return [_emp("depth_positivity", UNKNOWN, pos_claim, why), _emp("riemann_l1", UNKNOWN, l1_claim, why)]
    sys = read(spec)
    Hs = [substitute(H, {"g": lit(g)}) for H in sys["update"]]
    table, pos, l1 = [], [], []
    for k in cases:
        case, T = data(k), Fraction(k["T"])
        lo, hi = wave_speeds(*case, float(g))
        if not (float(x0) + lo * float(T) > 0 and float(x0) + hi * float(T) < 1):
            return [_emp("depth_positivity", UNKNOWN, pos_claim, f"{k.get('name')}: waves leave [0, 1] before T"),
                    _emp("riemann_l1", UNKNOWN, l1_claim, f"{k.get('name')}: waves leave [0, 1] before T")]
        hs, us = star_state(*case, float(g))
        for lam in [Fraction(v) for v in k["lams"]] if "lams" in k else lams:
            rows = [run(Hs, case, float(g), float(x0), float(T), float(lam), n) for n in grids]
            name = f"{k.get('name', 'case')}, dt/dx = {lam}"
            over = [r["N"] for r in rows if r["cfl"] > cfl]
            neg = [r for r in rows if r["bad_step"] is not None or not r["finite"]]
            low = min(r["min_h"] for r in rows)
            if neg and not over:
                pos.append((REFUTED_EMPIRICALLY, f"{name}: h <= 0 or not finite at N = {[r['N'] for r in neg]} "
                            f"(step {neg[0]['bad_step']}, min h {neg[0]['min_h']:.3g})"))
            elif over:
                pos.append((UNKNOWN, f"{name}: observed CFL number above {cfl} at N = {over}, outside the claim"))
            else:
                pos.append((NOT_REFUTED, f"{name}: min h = {low:.6g} > 0 over all steps and grids "
                            f"(observed CFL at most {max(r['cfl'] for r in rows):.3f})"))
            st, d = _l1_verdict(rows)
            far = (case[0], case[0] * case[1], case[2], case[2] * case[3])
            # only the grids the verdict uses: on coarse grids Lax-Friedrichs moves an exponentially small
            # signal one cell per step, which can reach the boundary without touching the error
            lost = [r["N"] for r in rows[-2:] if not r["finite"] or max(abs(a - b) for a, b in zip(r["ends"], far)) > 1e-6]
            if lost:
                st, d = UNKNOWN, f"waves reached the boundary or blew up at N = {lost}"
            l1.append((st, f"{name}: {d}"))
            table.append(f"{name}: x0 = {x0}, T = {T}, g = {g}; exact star state h* = {hs:.6f}, u* = {us:.6f}; "
                         f"outer waves at speeds {lo:.4f}, {hi:.4f}")
            table.append(f"{'N':>6} {'L1(h)':>11} {'L1(m)':>11} {'order':>6} {'min h':>10} {'max CFL':>8}")
            prev = None
            for r in rows:
                o = "" if prev is None or not prev > 0 or not r["L1"] > 0 else f"{math.log2(prev / r['L1']):.2f}"
                table.append(f"{r['N']:>6} {r['L1_h']:11.4e} {r['L1_m']:11.4e} {o:>6} {r['min_h']:10.6f} {r['cfl']:8.4f}")
                prev = r["L1"]
    study = {"study": LABEL + f" (each case at two dt/dx, default {', '.join(map(str, lams))})", "table": table}
    combine = lambda xs: (REFUTED_EMPIRICALLY if any(s == REFUTED_EMPIRICALLY for s, _ in xs)
                          else NOT_REFUTED if all(s == NOT_REFUTED for s, _ in xs) else UNKNOWN)
    return [_emp("depth_positivity", combine(pos), pos_claim, "; ".join(d for _, d in pos), study,
                 [f"observed on these runs only; not a proof of positivity (g = {g})"]),
            _emp("riemann_l1", combine(l1), l1_claim, "; ".join(d for _, d in l1), study,
                 [f"observed on these runs only (g = {g}); a falling L1 error on finite grids does not prove convergence"])]


def _emp(check, status, claim, detail, witness=None, assumptions=()):
    r = result(check, status, claim, detail, witness, assumptions)
    r["guarantee"] = EMPIRICAL
    return r


# ---------------------------------------------------------------- exact depth positivity (one induction step)

DEPTH = ("hm1", "h0", "hp1")
STEP_N = ("g",) + DEPTH                 # the only variables ever declared positive here: step-n depths and g
DEPTH_EPS = Fraction(1, 1024)


def _sqrt_root(p: P.Poly) -> P.Poly | None:
    """q with q^2 = p for a single monomial p = c*x1^(2k1)*... with c an exact square, else None."""
    if len(p) != 1:
        return None
    ((m, c),) = p.items()
    r = P._exact_sqrt(c) if c > 0 else None
    if r is None or any(a[0] != "v" or k % 2 for a, k in m):
        return None
    return {P._mono({a: k // 2 for a, k in m}): r}


def _depth_cells(e: E) -> tuple[list, dict]:
    """Sign cells of the depth update e (in h_j, u_j, lam, g), as checks.sign_cells, but a square root of a
    step-n quantity that is not a square is kept as a variable: sqrt(g*h_j) becomes s_j, any other one a
    fresh _t_k. Returns ([(poly, cell atoms)], {variable: (argument, strictly positive)}). The variables
    forget that s_j^2 = g*h_j: a relaxation, so a certificate over them is a certificate for the scheme."""
    names = {checks._key(P.mul(P.var("g"), P.var(h))): f"s_{h[1:]}" for h in DEPTH}
    roots: dict = {}

    def hook(assign):
        def h(node, rec):
            a = node.args[0]
            if a.kind == "powi" and a.q % 2 == 0:
                x = P.power(rec(a.args[0]), a.q // 2)
            else:
                p = rec(a)
                x = _sqrt_root(p)
                if x is None:
                    if not P.nonneg_by_form(p, positive=STEP_N):
                        raise P.Undecided(f"cannot show sqrt argument {P.show(p)} is non-negative from step-n data")
                    k = checks._key(p)
                    if k not in names:
                        names[k] = f"_t_{len(names) - len(DEPTH)}"
                    roots[names[k]] = (p, P.positive_by_form(p, positive=STEP_N))
                    return P.var(names[k])
            if set(x) <= {()}:
                return P.const(abs(x.get((), Fraction(0))))
            if P.positive_by_form(x, positive=STEP_N):
                return x
            for key, sgn in ((checks._key(x), 1), (checks._key(P.scale(x, -1)), -1)):
                if key in assign:
                    return P.scale(x, sgn * assign[key][1])
            raise checks._Split(x)
        return h

    todo, out = [{}], []
    while todo:
        assign = todo.pop(0)
        try:
            p = P.from_expr(e, hook(assign))
        except checks._Split as s:
            todo += [{**assign, checks._key(s.p): (s.p, sgn)} for sgn in (1, -1)]
            continue
        out.append((p, [P.scale(x, sgn) for x, sgn in assign.values()]))
    return out, roots


def _depth_scaled(p: P.Poly) -> P.Poly:
    """lam^k * p with u_j = w_j/lam and s_j = z_j/lam (k clears negative powers of lam; lam > 0 keeps the sign)."""
    q = P.subst(p, {f"{v}{j}": P.mul(P.var(f"{w}_{j}"), P.inverse(P.var("lam")))
                    for v, w in (("u", "w"), ("s_", "z")) for j in SLOTS})
    k = -min((dict(m).get(("v", "lam"), 0) for m in q), default=0)
    return P.mul(q, P.power(P.var("lam"), k))


def _depth_coefficients(Hc: P.Poly) -> dict | None:
    """{h_j: c_j} with Hc = sum_j c_j h_j and no depth in any c_j, or None."""
    out: dict = {}
    for m, c in Hc.items():
        d = dict(m)
        hs = [x for x in DEPTH if ("v", x) in d]
        if len(hs) != 1 or d[("v", hs[0])] != 1 or any(a[0] == "s" for a in d):
            return None
        del d[("v", hs[0])]
        out[hs[0]] = P.add(out.get(hs[0], {}), {P._mono(d): c})
    return out


def _depth_point(H: P.Poly, c: Fraction) -> dict | None:
    """An exact rational stencil state with h_j > 0, g = 1 and lam*(|u_j| + sqrt(g h_j)) <= c for every j
    whose update gives h_i^{n+1} <= 0. States are built from z_j = lam*sqrt(g h_j) > 0 and w_j = lam*u_j
    with |w_j| + z_j <= c, so every square root is rational; H is evaluated exactly at the point."""
    zs = [c, c / 2, c / 10, c / 100, c / 10000]
    opts = [(z, w) for z in zs for w in (-(c - z), Fraction(0), c - z)]
    for lam in (Fraction(1), Fraction(1, 3)):
        for pick in product(opts, repeat=3):
            pt = {"lam": lam, "g": Fraction(1)}
            for j, (z, w) in zip(SLOTS, pick):
                h = (z / lam) ** 2
                pt.update({f"h{j}": h, f"m{j}": h * w / lam})
            v = P.evaluate(H, pt)
            cfl = [lam * (abs(pt[f"m{j}"] / pt[f"h{j}"]) + z / lam) for j, (z, _) in zip(SLOTS, pick)]
            if v is not None and v <= 0 and all(x <= c for x in cfl) and all(pt[h] > 0 for h in DEPTH):
                return {"state": checks._fmt(pt), "h_i^{n+1}": str(v), "cfl_numbers": [str(x) for x in cfl]}
    return None


def _simplex(A: list, b: list, cost: list) -> tuple | None:
    """min cost.mu subject to A mu = b, mu >= 0, exactly (two-phase tableau simplex, Bland's rule).
    Returns ("optimal", mu), ("unbounded", mu, d) with mu feasible, d >= 0, A d = 0 and cost.d < 0, or
    None if infeasible. Only finds candidates: callers replay what they use."""
    m, n = len(A), len(cost)
    rows = [[-x for x in r] + [-y] if y < 0 else list(r) + [y] for r, y in zip(A, b)]
    T = [r[:n] + [Fraction(int(i == k)) for k in range(m)] + [r[n]] for i, r in enumerate(rows)]
    basis = list(range(n, n + m))

    def pivot(i, j):
        T[i] = [x / T[i][j] for x in T[i]]
        for k in range(len(T)):
            if k != i and T[k][j]:
                T[k] = [a - T[k][j] * c for a, c in zip(T[k], T[i])]
        basis[i] = j

    def run(c, cols):
        while True:
            red = {j: c[j] - sum(c[basis[i]] * T[i][j] for i in range(len(T))) for j in cols if j not in basis}
            j = next((j for j in sorted(red) if red[j] < 0), None)
            if j is None:
                return None
            ratios = [(T[i][-1] / T[i][j], basis[i], i) for i in range(len(T)) if T[i][j] > 0]
            if not ratios:
                return j
            pivot(min(ratios)[2], j)

    run([Fraction(0)] * n + [Fraction(1)] * m, range(n + m))
    if any(T[i][-1] for i in range(len(T)) if basis[i] >= n):
        return None
    for i in reversed(range(len(T))):                  # drive zero artificials out, or drop redundant rows
        if basis[i] >= n:
            j = next((j for j in range(n) if T[i][j]), None)
            if j is None:
                del T[i], basis[i]
            else:
                pivot(i, j)
    T[:] = [r[:n] + [r[-1]] for r in T]
    c = list(cost) + [Fraction(0)] * m
    j = run(c, range(n))
    mu = [Fraction(0)] * n
    for i, k in enumerate(basis):
        mu[k] = T[i][-1]
    if j is None:
        return "optimal", mu
    d = [Fraction(0)] * n
    d[j] = Fraction(1)
    for i, k in enumerate(basis):
        d[k] = -T[i][j]
    return "unbounded", mu, d


def _farkas_lp(p: P.Poly, atoms: list) -> dict | None:
    """The affine Farkas certificate of checks.certify_farkas, p = r + sum_j mu_j a_j with mu_j, r >= 0,
    found by linear programming (max r over the multipliers) instead of enumerating atom subsets. The
    identity is replayed in the normal form before it is returned, so the solver is not trusted."""
    names = sorted(P.variables(p).union(*(P.variables(a) for a in atoms)))
    lp = checks._linear(p, names)
    usable = [(a, la) for a in atoms if (la := checks._linear(a, names)) is not None]
    if lp is None:
        return None
    sol = _simplex([[la[1].get(v, Fraction(0)) for _, la in usable] for v in names],
                   [lp[1].get(v, Fraction(0)) for v in names], [la[0] for _, la in usable])
    if sol is None:
        return None
    mu = sol[1]
    if sol[0] == "unbounded":                           # r grows without bound along d: step until r >= 0
        r0 = lp[0] - sum(m * la[0] for m, (_, la) in zip(mu, usable))
        slope = -sum(x * la[0] for x, (_, la) in zip(sol[2], usable))
        mu = [m + max(Fraction(0), -r0 / slope) * x for m, x in zip(mu, sol[2])]
    r = lp[0] - sum((m * la[0] for m, (_, la) in zip(mu, usable)), Fraction(0))
    rest = p
    for m, (a, _) in zip(mu, usable):
        rest = P.add(rest, P.scale(a, m), -1)
    if r < 0 or any(m < 0 for m in mu) or rest != P.const(r):
        return None
    return {"farkas": f"{P.show(p)} = {r}" + "".join(f" + {m}*({P.show(a)})" for m, (a, _) in zip(mu, usable) if m),
            "multipliers": {P.show(a): str(m) for m, (a, _) in zip(mu, usable) if m}, "remainder": str(r)}


def _depth_certify(p: P.Poly, region: list) -> dict | None:
    """p >= 0 on the region: by form (z_j >= 0, any power of lam), else an affine Farkas identity."""
    if P.nonneg_by_form(p, nonneg={v for v in P.variables(p) if v.startswith(("z_", "_t_"))}, positive={"lam"}):
        return {"by_form": P.show(p)}
    return _farkas_lp(p, region)


def _depth_strict(coeffs: dict, region: list, zs: list) -> dict | None:
    """A certificate that some coefficient is > 0 everywhere on the region (every z_j > 0 there): p - eps*t >= 0
    with t = 1 or t = z_j > 0, for p one coefficient c_j (tried first: fewer atoms) or their sum S. Then
    h_i^{n+1} = sum_j c_j h_j > 0: every term is >= 0, and one term (all of S, if p = S) is > 0. As t >= 0,
    p - eps*t >= 0 for some eps > 0 implies it for every smaller eps, so one small eps is enough."""
    S = P.add(P.add(coeffs["hm1"], coeffs["h0"]), coeffs["hp1"])
    cands = sorted(((f"coefficient of {h}", p) for h, p in coeffs.items() if p), key=lambda x: len(P.variables(x[1])))
    for what, p in cands + [("sum of coefficients", S)]:
        cells = {v[2:] for v in P.variables(p) if v.startswith(("w_", "z_"))}
        for t in [P.var(z) for z in zs if z[2:] in cells] + [P.const(1)]:
            cert = _depth_certify(P.add(p, P.scale(t, DEPTH_EPS), -1), region)
            if cert:
                return {"bound": f"{what} >= {DEPTH_EPS}*{P.show(t)}", **cert}
    return None


def depth_positivity_exact(spec: dict, cfl=None) -> dict:
    """Exact depth positivity for a shallow-water scheme: the induction step

        if h_j^n > 0 for j = i-1, i, i+1, g > 0, and lam*(|u_j| + sqrt(g h_j)) <= c on that stencil,
        then h_i^{n+1} > 0.

    Induction over n then gives h > 0 for all time from positive initial data, as long as the CFL
    condition holds at every step (the claim's hypothesis). The hypothesis is on the stencil only, which
    is weaker than a CFL condition on the whole grid, so the theorem is stronger.

    The no-circularity rule. h^n > 0 and g > 0 are the only uses of the domain: `positive=` (and the
    square roots it admits) is applied to the step-n variables in STEP_N only, and h_i^{n+1} is never
    declared positive. The conclusion comes from an explicit algebraic form of h_i^{n+1}:

    1. With h_j > 0 every momentum is m_j = h_j u_j for a free real u_j; we substitute that.
    2. Every |x| = sqrt(x^2) is split into sign cells (closed, covering, as in checks.sign_cells). A
       square root of a step-n quantity that is not a square is kept as a variable: s_j for sqrt(g h_j),
       which is > 0 because g, h_j > 0. We forget s_j^2 = g h_j (and treat s_j as any positive number):
       a weaker hypothesis, so a certificate over the relaxed variables proves the claim.
    3. On each cell h_i^{n+1} = sum_j c_j h_j, with c_j free of the depths. With w_j = lam*u_j and
       z_j = lam*s_j the CFL condition is the affine region c - w_j - z_j >= 0, c + w_j - z_j >= 0
       (|w_j| >= +-w_j), z_j >= 0, and c_j is affine in (w, z) for the three-point fluxes here. For
       Rusanov the interface speed max(|u| + sqrt(g h)) is resolved by the sign cells, so on each cell it
       is one neighbour's |u| + sqrt(g h), bounded by c/lam.
    4. Each c_j >= 0 is certified on the cell intersected with the CFL region, by form or by an affine
       Farkas identity c_j = r + sum_k mu_k a_k (mu_k, r >= 0; found by an exact LP and replayed in the
       normal form); a cell with contradictory atoms (a Farkas identity for -1 >= 0) is empty and skipped.
       Then h_i^{n+1} >= 0. For h_i^{n+1} > 0 we certify p >= eps*t for p one c_j (or their sum) and
       t = 1 or t = z_j > 0: then that term (or some term) of sum_j c_j h_j is > 0, as h_j > 0.

    REFUTED needs an exact rational stencil state with h_j > 0, g = 1 and the CFL condition holding at
    every cell of the stencil whose exact update has h_i^{n+1} <= 0. Embedded in a grid a, ..., a, b, c,
    ..., c (constant extension, so every cell's state is one of the three and the CFL condition holds
    everywhere) it is positive initial data whose first step has h <= 0: the claim fails. Wet/dry data
    (h = 0 allowed, i.e. the domain does not state h > 0) is outside the claim: NOT_APPLICABLE."""
    c = cfl if cfl is not None else spec.get("claims", {}).get("riemann", {}).get("cfl")
    claim = (f"induction step for depth positivity: h_j^n > 0 and lam*(|u_j| + sqrt(g h_j)) <= {c} for j = i-1, i, "
             "i+1 imply h_i^{n+1} > 0, so h > 0 for all time from positive data while the CFL condition holds")
    pde = spec["pde"]
    if c is None:
        return result("depth_positivity_exact", NOT_APPLICABLE, claim, "no CFL number claimed (claims.riemann.cfl)")
    c = Fraction(c)
    if pde.get("domain", {}).get("h") != "positive" or pde.get("parameters", {}).get("g") != "positive":
        return result("depth_positivity_exact", NOT_APPLICABLE, claim, "the domain does not state h > 0 and g > 0: "
                      "wet/dry states (h = 0) are outside the claim, and the induction hypothesis needs h^n > 0")
    if not _shallow_water(spec) or c <= 0:
        return result("depth_positivity_exact", UNKNOWN, claim, "the CFL condition is defined for shallow water "
                      "f = (m, m^2/h + g h^2/2) with a positive CFL number only")
    assumptions = ["induction hypothesis: g > 0 and h_j^n > 0 at the stencil cells i-1, i, i+1 (step n only)",
                   f"lam = dt/dx > 0 and lam*(|u_j| + sqrt(g h_j)) <= {c} at those cells",
                   "the certificate keeps only z_j = lam*sqrt(g h_j) > 0 (it forgets z_j^2 = lam^2 g h_j): a weaker "
                   "hypothesis, so a stronger theorem"]
    try:
        e = read(spec)["update"][0]
        stray = expr_variables(e) - set(STEP_N) - {"mm1", "m0", "mp1", "lam"}
        if stray:
            return result("depth_positivity_exact", UNKNOWN, claim, f"the depth update uses {sorted(stray)}, which "
                          "are not step-n stencil data", assumptions=assumptions)
        H = P.from_expr(e, positive=STEP_N)
        cells, roots = _depth_cells(substitute(e, {f"m{j}": E("mul", (var(f"h{j}"), var(f"u{j}"))) for j in SLOTS}))
    except P.Undecided as ex:
        return result("depth_positivity_exact", UNKNOWN, claim, str(ex), assumptions=assumptions)
    zs, ws = [f"z_{j}" for j in SLOTS], [f"w_{j}" for j in SLOTS]
    region = ([P.add(P.const(c), P.add(P.scale(P.var(w), s), P.var(z)), -1) for w, z in zip(ws, zs) for s in (1, -1)]
              + [P.var(z) for z in zs] + [P.var("lam")] + [P.var(t) for t in roots])
    wit = {"h_i^{n+1}": P.show(H), "substitution": "m_j = h_j*u_j, w_j = lam*u_j, z_j = lam*sqrt(g h_j)",
           "cfl_region": [checks._show_atom(a) for a in region], "cells": []}
    failed = []
    try:
        for Hc, atoms in cells:
            reg = [_depth_scaled(a) for a in atoms] + region
            coeffs = _depth_coefficients(Hc)
            row = {"cell": [checks._show_atom(a) for a in atoms], "h_i^{n+1}": P.show(Hc)}
            wit["cells"].append(row)
            if coeffs is None:
                failed.append("not linear in the depths")
                break
            scaled = {h: _depth_scaled(coeffs.get(h, {})) for h in DEPTH}
            row["coefficients"] = {h: P.show(p) for h, p in scaled.items()}
            certs = {}
            for h, p in scaled.items():                  # stop at the first failure: VERIFIED is then out of reach
                certs[h] = _depth_certify(p, reg)
                if certs[h] is None:
                    break
            if None in certs.values():
                if empty := _farkas_lp(P.const(-1), reg):
                    row["empty"] = empty
                    continue
                failed.append(f"coefficient of {h}")
                break
            strict = _depth_strict(scaled, reg, zs)
            row.update(certificates=certs, strict=strict or "none found")
            if strict is None:
                failed.append("strict positivity")
                break
    except P.Undecided as ex:
        return result("depth_positivity_exact", UNKNOWN, claim, str(ex), wit, assumptions)
    if not failed:
        return result("depth_positivity_exact", VERIFIED, claim,
                      f"on each of {len(cells)} closed sign cells h_i^{{n+1}} = sum_j c_j h_j^n with every c_j >= 0 and "
                      "sum_j c_j > 0 on the CFL region (certificates below), so h_i^{n+1} > 0", wit, assumptions)
    hit = _depth_point(H, c)
    if hit:
        wit["counterexample"] = hit
        return result("depth_positivity_exact", REFUTED, claim,
                      f"h_i^{{n+1}} = {hit['h_i^{n+1}']} <= 0 at the exact positive stencil state {hit['state']} "
                      f"with CFL numbers {hit['cfl_numbers']} <= {c}", wit, assumptions)
    return result("depth_positivity_exact", UNKNOWN, claim, f"no certificate (cell {len(wit['cells'])}: {failed[0]}) "
                  "and no exact counterexample found", wit, assumptions)


def check_all(spec: dict) -> list[dict]:
    out = [hyperbolicity(spec), consistency(spec), conservation(spec)]
    if "riemann" in spec.get("claims", {}):
        out += riemann_studies(spec)
    if "positive_depth_under_cfl" in spec.get("named_claims", []):
        out.append(depth_positivity_exact(spec))
    return out
