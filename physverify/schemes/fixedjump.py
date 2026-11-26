"""Exact refutation of `limit_is_weak_solution`, `selects_entropy_solution` and `correct_shock_speed`:
a stationary jump that violates Rankine-Hugoniot.

`stationary_rh_violation` looks for Riemann data uL | uR (uL != uR) that the fully discrete update
never changes, with f(uL) != f(uR). It works on the update H as written, so it covers
non-conservative schemes, which is what it is for: no flux form is needed.
`stationary_shock_rh_violation` is the same search restricted to Lax shocks (below).

The argument. Put the jump at a cell interface (x0 = 0), so the same step is represented exactly on
every grid. A stencil of half-width r (3-point: r = 1, 5-point: r = 2) sees only 2r + 2 distinct
windows of the step: the two far-field constants (uL, ..., uL) and (uR, ..., uR), and the 2r windows
that straddle the jump. If H returns its centre value on each of them, then u^1 = u^0, so u^n = u^0
for every n and every dx at fixed dt/dx (on the infinite grid, or with transmissive boundaries, which
only see constant states). The identities are normal forms in lam = dt/dx, so they hold at every
dt/dx. The numerical solutions converge, trivially, in L1_loc to the stationary jump, which is
bounded. A stationary jump is a weak solution of u_t + f(u)_x = 0 iff f(uL) = f(uR) (the
Rankine-Hugoniot condition at speed 0). So if f(uL) != f(uR):
- that limit is not a weak solution, so `limit_is_weak_solution` is false for this scheme;
- the entropy solution is a weak solution, so the limit is not the entropy solution either, and
  `selects_entropy_solution` is false;
- for `correct_shock_speed` this is not enough: if uL | uR is an expansion, the exact solution is a
  rarefaction with no shock in it, and a scheme that freezes the jump has a wrong limit but no shock
  at a wrong speed. So `stationary_shock_rh_violation` refutes only on a pair that is a Lax shock:
  f'' >= 0 on [min(uL, uR), max(uL, uR)], certified by non-negative Bernstein coefficients, and
  f'(uL) > f'(uR) (hence uL > uR). Then the entropy solution, which only takes values in that
  interval, is the single shock uL | uR moving at s = (f(uL) - f(uR))/(uL - uR), and s != 0, while
  the scheme's discontinuity stays at speed 0. If f is not certified convex there, or no frozen
  pair is a Lax shock, it is NOT_APPLICABLE.

For a conservative scheme the windows across the jump force F(uL, uL) = F(uL, uR) = F(uR, uR), so with
a consistent flux f(uL) = f(uR) and the check never refutes it: the frozen step is then a weak
solution (perhaps not the entropy one, which is `checks.steady_nonentropy_step`'s business).

Candidates: the spec's shock-study pairs, then pairs from FIXED_JUMP_GRID. Each refutation is replayed
by evaluating H at every window, and f at uL and uR, in exact rationals (`poly.evaluate`), at the
study's dt/dx values and at REPLAY_LAMS. If no pair is found the check is NOT_APPLICABLE: a failed
search proves nothing, and it never verifies.
"""

from __future__ import annotations

from fractions import Fraction

from . import checks, poly as P
from .checks import NOT_APPLICABLE, REFUTED, STENCIL, STENCIL5, UNKNOWN, result

FIXED_JUMP_GRID = tuple(Fraction(x) for x in ("-1", "0", "1/2", "1", "2"))
REPLAY_LAMS = (Fraction(1, 2), Fraction(1))
CLAIM = ("no stationary jump violates Rankine-Hugoniot: no Riemann data uL | uR with f(uL) != f(uR) is an exact "
         "fixed point of the update at every dt/dx (necessary for every bounded limit being a weak solution, and "
         "for the limit being the entropy solution)")
SHOCK_CLAIM = ("no stationary Lax shock violates Rankine-Hugoniot: no Riemann data uL | uR with f convex on [uR, uL], "
               "f'(uL) > f'(uR) and f(uL) != f(uR) is an exact fixed point of the update at every dt/dx (necessary "
               "for shocks moving at the Rankine-Hugoniot speed)")


def windows(stencil: tuple) -> list[tuple[str, str]]:
    """(window, centre) for every stencil position of the step uL | uR, as strings of L and R: the
    far-field constants first, then the 2r windows across the jump."""
    n, r = len(stencil), len(stencil) // 2
    out = [("L" * n, "L"), ("R" * n, "R")]
    for k in range(1, n):                                    # k cells of the window lie right of the jump
        w = "L" * (n - k) + "R" * k
        out.append((w, w[r]))
    return out


def _identities(H: P.Poly, stencil: tuple, uL: Fraction, uR: Fraction) -> dict:
    """{window: normal form in lam of H(window) - centre}."""
    if stencil == STENCIL:                                   # the steady-step identities, as they are
        ids = checks.steady_identities(H, uL, uR)
        return {w: ids[name] for name, w, _ in checks.STEADY_STENCILS}
    v = {"L": uL, "R": uR}
    return {w: P.add(P.subst(H, {x: P.const(v[c]) for x, c in zip(stencil, w)}), P.const(v[t]), -1)
            for w, t in windows(stencil)}


def _replay(H: P.Poly, f: P.Poly, stencil: tuple, uL: Fraction, uR: Fraction, lams) -> dict | None:
    """Evaluate H at every window and f at uL, uR directly; the witness table, or None if any
    fixed-point value or f(uL) != f(uR) fails to replay."""
    v = {"L": uL, "R": uR}
    rows = {}
    for lam in lams:
        for w, t in windows(stencil):
            h = P.evaluate(H, {**{x: v[c] for x, c in zip(stencil, w)}, "lam": lam})
            if h != v[t]:
                return None
            rows[f"H({', '.join(str(v[c]) for c in w)}) at dt/dx = {lam}"] = str(h)
    fL, fR = P.evaluate(f, {"u": uL}), P.evaluate(f, {"u": uR})
    if fL is None or fR is None or fL == fR:
        return None
    return rows


def _coefficients(p: P.Poly, x: str) -> list | None:
    """[c_0, c_1, ...] with p = sum_k c_k x^k, or None if p is not a polynomial in x alone."""
    c: list = []
    for m, v in p.items():
        if any(a != ("v", x) or k < 0 for a, k in m):
            return None
        k = m[0][1] if m else 0
        c += [Fraction(0)] * (k + 1 - len(c))
        c[k] += v
    return c


def lax_shock(f: P.Poly, uL: Fraction, uR: Fraction) -> dict | None:
    """The certificate that uL | uR is a Lax shock of a convex f, or None: f'' has non-negative
    Bernstein coefficients on [min, max] of the pair (so f is convex there) and f'(uL) > f'(uR)."""
    fp = P.derivative(f, "u")
    c = _coefficients(P.derivative(fp, "u"), "u")
    dL, dR = P.evaluate(fp, {"u": uL}), P.evaluate(fp, {"u": uR})
    if c is None or dL is None or dR is None or not dL > dR:
        return None
    lo, hi = min(uL, uR), max(uL, uR)
    b = checks.bernstein(c or [Fraction(0)], lo, hi)
    if min(b) < 0:
        return None
    return {"f'(uL)": str(dL), "f'(uR)": str(dR), "f''(u)": P.show(P.derivative(fp, "u")),
            f"Bernstein coefficients of f'' on [{lo}, {hi}]": [str(x) for x in b]}


def stationary_rh_violation(spec: dict) -> dict:
    """Any frozen pair with f(uL) != f(uR), shock or expansion."""
    return _search(spec, "stationary_rh_violation", CLAIM, shocks_only=False)


def stationary_shock_rh_violation(spec: dict) -> dict:
    """Only a frozen pair that is a Lax shock of a convex f (its own id, so `correct_shock_speed` sees
    only this one)."""
    return _search(spec, "stationary_shock_rh_violation", SHOCK_CLAIM, shocks_only=True)


def _search(spec: dict, check: str, claim: str, shocks_only: bool) -> dict:
    try:
        f = P.from_expr(checks.pde_flux(spec))
        H = P.from_expr(checks.update(spec))
    except P.Undecided as ex:
        return result(check, UNKNOWN, claim, str(ex))
    stencil = checks.stencil_of(P.variables(H))
    if P.variables(f) - {"u"} or P.variables(H) - set(stencil) - {"lam"}:
        return result(check, UNKNOWN, claim, "the flux or the update has free parameters")
    cases = spec.get("claims", {}).get("shock_speed", {}).get("cases", [])
    given = [(Fraction(k["uL"]), Fraction(k["uR"])) for k in cases]
    lams = sorted({Fraction(k["lam"]) for k in cases if Fraction(k["lam"]) > 0} | set(REPLAY_LAMS))
    grid = [(a, b) for a in FIXED_JUMP_GRID for b in FIXED_JUMP_GRID]
    tried = 0
    for found_by, pairs in (("shock-study pair", given), ("search over a small grid", grid)):
        for uL, uR in pairs:
            fL, fR = P.evaluate(f, {"u": uL}), P.evaluate(f, {"u": uR})
            if uL == uR or fL is None or fR is None or fL == fR:
                continue
            try:
                shock = lax_shock(f, uL, uR) if shocks_only else None
            except P.Undecided:                              # f' of a |.|: not certified convex
                shock = None
            if shocks_only and shock is None:
                continue
            tried += 1
            try:
                ids = _identities(H, stencil, uL, uR)
            except P.Undecided:
                continue
            if any(ids.values()):
                continue
            replay = _replay(H, f, stencil, uL, uR, lams)
            if replay is None:                               # cannot happen if the normal forms are right
                continue
            s = (fL - fR) / (uL - uR)
            wit = {"uL": str(uL), "uR": str(uR), "found_by": found_by, "stencil": list(stencil),
                   "identities": {f"H({', '.join(w)}) - {t}": "0 in lam" for w, t in windows(stencil)},
                   "replay": replay, "f(uL)": str(fL), "f(uR)": str(fR), "Rankine-Hugoniot speed": str(s)}
            assumptions = ["the jump sits at a cell interface (x0 = 0) on every grid, so the step is represented "
                           "exactly for every dx; the grid is infinite or its boundaries are transmissive",
                           "refinement dx -> 0 at a fixed dt/dx (any dt/dx > 0: the identities hold in lam)"]
            if shocks_only:
                wit["Lax shock"] = shock
                dL, dR = shock["f'(uL)"], shock["f'(uR)"]
                return result(check, REFUTED, claim,
                              f"the step uL = {uL} | uR = {uR} is an exact fixed point of the update at every dt/dx "
                              f"({found_by}); f is convex on [{uR}, {uL}] and f'(uL) = {dL} > f'(uR) = {dR}, "
                              "so the entropy solution is a single shock "
                              f"moving at s = {s} != 0, while the scheme's discontinuity stays at speed 0", wit,
                              assumptions + [f"f'' >= 0 on [{uR}, {uL}] (non-negative Bernstein coefficients) and "
                                             "f'(uL) > f'(uR): the entropy solution of this Riemann problem is the "
                                             "single shock uL | uR at the Rankine-Hugoniot speed"])
            return result(check, REFUTED, claim,
                          f"the step uL = {uL} | uR = {uR} is an exact fixed point of the update at every dt/dx "
                          f"({found_by}), but f(uL) = {fL} != f(uR) = {fR}: the scheme's limit on this data is a "
                          f"stationary jump, not a weak solution (Rankine-Hugoniot would need speed s = {s})", wit,
                          assumptions)
    what = ("Lax-shock pairs (f'' >= 0 certified on the pair's interval, f'(uL) > f'(uR))" if shocks_only
            else "rational pairs")
    return result(check, NOT_APPLICABLE, claim,
                  f"no fixed-point step among {tried} {what} with f(uL) != f(uR) (the shock-study pairs, "
                  "then a small grid); a failed search proves nothing, so this decides nothing")
