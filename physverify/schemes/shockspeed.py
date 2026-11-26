"""Exact preconditions for the convergence rows of `correct_shock_speed` and `limit_is_weak_solution`.

- `flux_lipschitz`: the numerical flux is locally Lipschitz in the states, by form. The rows' theorems
  (Lax-Wendroff, Crandall-Majda, the Helly argument for TVD schemes) all assume it.
- `shock_scope_monotone`, `shock_scope_tvd`: every dt/dx of the spec's shock study lies inside the
  range the monotonicity (or TVD) check certified, for the study's data. The theorems speak about
  refinement at a fixed dt/dx inside that range; a row whose study runs outside it says nothing, so
  these give NOT_APPLICABLE (never a failure) there, like `linear.lax_richtmyer_scope`.
"""

from __future__ import annotations

from fractions import Fraction

from ..expr import intern, to_str, variables
from . import checks, limiters, poly as P
from .checks import NOT_APPLICABLE, UNKNOWN, VERIFIED, result

PARAMS = {"lam"}                 # fixed for a given refinement at fixed dt/dx; every other variable is a state

LIPSCHITZ_RULES = ("polynomials are locally Lipschitz; sums, differences and products of locally Lipschitz "
                   "functions are; so is a non-negative integer power; |g| = sqrt(g^2) is when g is (|.| is "
                   "1-Lipschitz); a factor free of the states (a function of dt/dx only, fixed in the refinement) "
                   "changes only the constant")


def _state_free(e) -> bool:
    return not (variables(e) - PARAMS)


def _lipschitz(e, memo: dict) -> str | None:
    """None if e is locally Lipschitz in the states by the rules above, else the subexpression that is
    not covered. Memoized by node identity (pass an `intern`ed expression)."""
    if id(e) in memo:
        return memo[id(e)]
    k, a = e.kind, e.args
    if k in ("var", "lit", "pi") or _state_free(e):
        bad = None
    elif k in ("neg", "add", "sub", "mul"):
        bad = next((b for x in a if (b := _lipschitz(x, memo))), None)
    elif k == "powi" and e.q >= 0:
        bad = _lipschitz(a[0], memo)
    elif k == "div" and _state_free(a[1]):
        try:                                         # a constant factor only if the divisor is not 0
            d = P.from_expr(a[1])
        except P.Undecided:
            d = None
        bad = _lipschitz(a[0], memo) if d and len(d) == 1 else to_str(e)
    elif k == "sqrt" and a[0].kind == "powi" and a[0].q > 0 and a[0].q % 2 == 0:
        bad = _lipschitz(a[0].args[0], memo)        # sqrt(g^(2m)) = |g^m|
    else:
        bad = to_str(e)
    memo[id(e)] = bad
    return bad


def flux_lipschitz(spec: dict) -> dict:
    """The numerical flux is locally Lipschitz in the states, at every fixed dt/dx, by form.

    A declared numerical flux is checked as it is written. Without one, a three-point update H is
    checked: for a conservative consistent scheme H(a, a, b) = a - lam*(F(a, b) - f(a)), so
    F(a, b) = f(a) + (a - H(a, a, b))/lam is locally Lipschitz when H and f are. The rules
    (LIPSCHITZ_RULES) are structural: the expression is built from polynomials, |.| (which is how
    min, max and minmod are written), and factors in dt/dx only. Such a flux is continuous and
    piecewise polynomial; the sign-cell code in limiters.py also asserts that neighbouring cells agree
    where they meet. Anything else (a square root of something other than an even power, a division
    by a state-dependent expression, a rational power, sin, exp, ...) gives UNKNOWN: the rules do not
    cover it, which is not a proof that it fails. Local is enough for the rows that use this: each
    also needs an L-infinity bound, from the maximum principle (monotone) or TVD."""
    claim = "the numerical flux is locally Lipschitz in the states at every fixed dt/dx (by form)"
    F = checks.numerical_flux(spec)
    if F is not None:
        what, e = "declared numerical flux", F
    else:
        try:
            e = checks.update(spec)
            stencil = checks.stencil_of(P.variables(P.from_expr(e)))
        except P.Undecided as ex:
            return result("flux_lipschitz", UNKNOWN, claim, str(ex))
        if stencil != checks.STENCIL:
            return result("flux_lipschitz", UNKNOWN, claim, "no declared numerical flux, and the update is not a "
                          "three-point one, so no flux is recovered from it")
        what = ("three-point update H, so the flux F(a, b) = f(a) + (a - H(a, a, b))/lam it has if it is conservative "
                "and consistent (every row using this check also requires those)")
        bad = _lipschitz(intern(checks.pde_flux(spec)), {})
        if bad:
            return result("flux_lipschitz", UNKNOWN, claim, f"the PDE flux is not covered by the rules at {bad!r}")
    bad = _lipschitz(intern(e), {})
    if bad:
        return result("flux_lipschitz", UNKNOWN, claim,
                      f"the {what} is not locally Lipschitz by form at {bad!r} (a square root of something other "
                      "than an even power, a division by the states, or a function outside the polynomial "
                      "fragment); this decides nothing")
    return result("flux_lipschitz", VERIFIED, claim, f"the {what} {to_str(e)} is locally Lipschitz by form",
                  {"checked": what, "expression": to_str(e), "rules": LIPSCHITZ_RULES},
                  ["dt/dx is fixed and > 0 (the refinement keeps dt/dx constant)"])


def _cases(spec: dict) -> list:
    return [tuple(Fraction(k[v]) for v in ("uL", "uR", "lam"))
            for k in spec.get("claims", {}).get("shock_speed", {}).get("cases", [])]


def shock_scope_monotone(spec: dict) -> dict:
    """Each shock-study case (uL, uR, dt/dx) lies inside the monotone CFL region the monotonicity check
    certifies: lam*|f'(u)| <= c (c = claims.monotone_cfl) for every u between uR and uL. f' is affine
    (else the monotonicity check is UNKNOWN anyway), so the bound on the interval is its value at the
    endpoints. A monotone consistent scheme keeps its values in [min, max] of the data (maximum
    principle), so every later stencil stays in the region as well."""
    check, claim = "shock_scope_monotone", "every dt/dx of the shock study is inside the certified monotone range"
    c, cases = spec.get("claims", {}).get("monotone_cfl"), _cases(spec)
    if c is None or not cases:
        return result(check, NOT_APPLICABLE, claim, "no monotone CFL bound (claims.monotone_cfl) or no shock study cases")
    c = Fraction(c)
    try:
        fp = P.derivative(P.from_expr(checks.pde_flux(spec)), "u")
    except P.Undecided as ex:
        return result(check, NOT_APPLICABLE, claim, str(ex))
    if P.variables(fp) - {"u"} or any(x[0] != "v" or k > 1 for m in fp for x, k in m):
        return result(check, NOT_APPLICABLE, claim, f"f' = {P.show(fp)} is not affine in u")
    rows, why = [], []
    for uL, uR, lam in cases:
        m = max(abs(P.evaluate(fp, {"u": uL})), abs(P.evaluate(fp, {"u": uR})))
        rows.append(f"(uL, uR) = ({uL}, {uR}), dt/dx = {lam}: dt/dx * max|f'| = {lam * m} (bound {c})")
        if not (lam > 0 and lam * m <= c):
            why.append(rows[-1])
    if why:
        return result(check, NOT_APPLICABLE, claim, "outside the certified monotone range: " + "; ".join(why))
    return result(check, VERIFIED, claim, "every shock-study case is inside the monotone range (structural, exact)",
                  {"f'(u)": P.show(fp), "monotone_cfl": str(c), "cases": rows})


def shock_scope_tvd(spec: dict) -> dict:
    """Each shock-study dt/dx gives nu = a*dt/dx inside the claimed TVD range (claims.tvd_cfl), the
    range `limiters.tvd_harten` certifies. Linear advection only (f = a*u), like that check."""
    check, claim = "shock_scope_tvd", "every dt/dx of the shock study is inside the certified TVD range"
    r, cases = limiters._tvd_range(spec), _cases(spec)
    if r is None or not cases:
        return result(check, NOT_APPLICABLE, claim, "no TVD range (claims.tvd_cfl) or no shock study cases")
    try:
        a = limiters._advection(spec)
    except (checks.NonlinearFlux, P.Undecided) as ex:
        return result(check, NOT_APPLICABLE, claim, f"{ex}: the TVD check is for f = a*u")
    rows = [f"(uL, uR) = ({uL}, {uR}), dt/dx = {lam}: nu = {a * lam}" for uL, uR, lam in cases]
    why = [row for row, (_, _, lam) in zip(rows, cases) if not (lam > 0 and r[0] <= a * lam <= r[1])]
    if why:
        return result(check, NOT_APPLICABLE, claim, f"outside the certified TVD range [{r[0]}, {r[1]}]: " + "; ".join(why))
    return result(check, VERIFIED, claim, "every shock-study case is inside the TVD range (structural, exact)",
                  {"a": str(a), "tvd_cfl": [str(x) for x in r], "cases": rows})
