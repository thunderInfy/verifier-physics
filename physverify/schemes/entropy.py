"""Rarefaction study for Burgers (numpy floats; evidence, not proof).

For data uL < uR the entropy solution of u_t + (u^2/2)_x = 0 is the rarefaction fan
u = clip((x - x0)/t, uL, uR). Weak solutions are not unique: the standing or moving step is also
one (an expansion shock), and conservation alone does not exclude it. A scheme whose limit is the
entropy solution converges to the fan; a scheme that keeps the step has an L1 error that settles at
a non-zero value (for the stationary step on (-1, 1): the area between step and fan, T/2).

The scheme runs on [0, 1] with the jump at the cell interface x0 and transmissive
(constant-extrapolation) ghost cells, as in shock.py; T keeps the fan inside the domain, and the
study is UNKNOWN if the end cells drift from uL or uR by more than 1e-6*(uR - uL). Each case runs at
every dt/dx in `lams` (default 2/5 and 37/100: a fixed point of the update, or an error that looks
exact, must survive a deliberately incommensurate dt/dx before we call it exact).

Verdict per case and dt/dx, from the L1 errors e1, e2 on the last two grids (dx halved):
NOT_REFUTED when the observed order log2(e1/e2) >= ORDER (the error is falling);
REFUTED_EMPIRICALLY when |e2 - e1| < 0.1*e2 (it has settled at a non-zero value); UNKNOWN otherwise.
"""

from __future__ import annotations

import math
from fractions import Fraction

import numpy as np

from ..expr import parse
from . import checks, poly as P
from .convergence import EMPIRICAL, NOT_REFUTED, REFUTED_EMPIRICALLY, UNKNOWN, _steps, ev

ORDER = 0.3
GRIDS = (200, 400, 800, 1600)
LAMS = ("2/5", "37/100")
LABEL = ("Riemann problem uL < uR on [0, 1], jump at x0, transmissive (constant-extrapolation) boundaries; "
         "L1 error at T against the exact rarefaction fan u = clip((x - x0)/t, uL, uR) at cell centres")


def fan(x: np.ndarray, t: float, uL: float, uR: float, x0: float) -> np.ndarray:
    return np.clip((x - x0) / t, uL, uR)


def run(H, uL: float, uR: float, x0: float, T: float, lam: float, n: int) -> dict:
    dx = 1 / n
    assert abs(x0 * n - round(x0 * n)) < 1e-9, "x0 must be a cell interface"
    x = (np.arange(n) + 0.5) * dx
    u = np.where(x < x0, uL, uR)
    steps, dt = _steps(T, lam * dx)
    with np.errstate(all="ignore"):
        for _ in range(steps):
            u = ev(H, {"um1": np.concatenate(([u[0]], u[:-1])), "u0": u,
                       "up1": np.concatenate((u[1:], [u[-1]])), "lam": dt / dx})
    d = np.abs(u - fan(x, T, uL, uR, x0))
    return {"N": n, "L1": float(np.sum(d) * dx), "Linf": float(np.max(d)),
            "max_jump": float(np.max(np.abs(np.diff(u)))), "ends": (float(u[0]), float(u[-1])),
            "finite": bool(np.all(np.isfinite(u)))}


def verdict(rows: list) -> tuple[str, str]:
    a, b = rows[-2:]
    e1, e2 = a["L1"], b["L1"]
    if not (math.isfinite(e1) and math.isfinite(e2)) or e1 <= 0 or e2 <= 0:
        return UNKNOWN, "error vanished or is not finite"
    p = math.log(e1 / e2) / math.log(b["N"] / a["N"])
    msg = (f"L1 error {e1:.3e} at N = {a['N']}, {e2:.3e} at N = {b['N']} (observed order {p:.2f}); "
           f"largest jump between neighbouring cells at N = {b['N']}: {b['max_jump']:.3g}")
    if p >= ORDER:
        return NOT_REFUTED, msg
    if abs(e2 - e1) < 0.1 * e2:
        return REFUTED_EMPIRICALLY, msg + " (settled at a non-zero value: the limit is not the rarefaction)"
    return UNKNOWN, msg + " (inconclusive)"


def study(spec: dict, grids=GRIDS) -> dict:
    c = spec["claims"]["entropy_rarefaction"]
    x0 = Fraction(c.get("x0", "1/2"))
    lams = [Fraction(v) for v in c.get("lams", LAMS)]
    claim = "converges to the rarefaction fan (the entropy solution) on Riemann problems " + ", ".join(
        f"(uL, uR) = ({k['uL']}, {k['uR']})" for k in c["cases"])
    if P.add(P.from_expr(checks.pde_flux(spec)), P.from_expr(parse("u^2/2")), -1):
        return checks.result("entropy_rarefaction", UNKNOWN, claim, "the exact fan is only implemented for Burgers' u^2/2")
    H = checks.update(spec)
    table, statuses, details = [], [], []
    for k in c["cases"]:
        uL, uR, T = (Fraction(k[v]) for v in ("uL", "uR", "T"))
        if not uL < uR:
            return checks.result("entropy_rarefaction", UNKNOWN, claim, f"({uL}, {uR}) is not rarefaction data")
        for lam in lams:
            rows = [run(H, float(uL), float(uR), float(x0), float(T), float(lam), n) for n in grids]
            st, d = verdict(rows)
            lost = [r["N"] for r in rows if not r["finite"]
                    or max(abs(r["ends"][0] - float(uL)), abs(r["ends"][1] - float(uR))) > 1e-6 * float(uR - uL)]
            if lost:
                st, d = UNKNOWN, f"waves reached the boundary or blew up at N = {lost}"
            statuses.append(st)
            details.append(f"(uL, uR) = ({uL}, {uR}), dt/dx = {lam}: {d}")
            table.append(f"uL = {uL}, uR = {uR}, x0 = {x0}, T = {T}, dt/dx = {lam}: fan on "
                         f"[{x0 + uL * T}, {x0 + uR * T}]")
            table.append(f"{'N':>6} {'L1 error':>22} {'order':>6} {'Linf error':>11} {'max jump':>9}")
            prev = None
            for r in rows:
                o = "" if prev is None or prev <= 0 or r["L1"] <= 0 else f"{math.log2(prev / r['L1']):.2f}"
                table.append(f"{r['N']:>6} {r['L1']:22.15e} {o:>6} {r['Linf']:11.3e} {r['max_jump']:9.3g}")
                prev = r["L1"]
    status = (REFUTED_EMPIRICALLY if REFUTED_EMPIRICALLY in statuses
              else NOT_REFUTED if all(x == NOT_REFUTED for x in statuses) else UNKNOWN)
    r = checks.result("entropy_rarefaction", status, claim, "; ".join(details),
                      {"study": LABEL + f" (each case at dt/dx = {', '.join(map(str, lams))})", "table": table})
    r["guarantee"] = EMPIRICAL
    return r
