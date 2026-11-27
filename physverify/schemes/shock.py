"""Riemann-problem shock-speed study (numpy floats; evidence, not proof).

For data uL > uR on [0, 1] with the jump at x0 (a cell interface), the entropy solution of a
convex law such as Burgers is a single shock moving at the Rankine-Hugoniot speed
s = (f(uL) - f(uR)) / (uL - uR), computed here from the spec's PDE flux in Fraction arithmetic.
The scheme runs at fixed dt/dx on a non-periodic grid with transmissive (constant-extrapolation)
ghost cells; the claim's T is chosen so the shock stays inside the domain, and the study is
UNKNOWN if the end cells drift from uL or uR by more than 1e-6*(uL - uR).

The shock position x_s(t) at level l is where u crosses uR + l*(uL - uR), interpolated linearly
between the two cells (the steepest crossing if there are several). Two speeds come out of it:
- the late-window speed: the least-squares slope of x_s(t) over every step in [t_h, T], where t_h
  is the step nearest T/2, at levels l = 0.2, 0.5 and 0.8. The verdict uses it.
- the full-window speed (x_s(T) - x_s(0)) / T at l = 0.5, shown only. The step relaxes into a
  profile a few cells wide, which shifts the crossing by O(dx) at the start; divided by T that
  looks like an O(dx) speed error whose sign depends on the level.
A least-squares slope rather than (x_s(T) - x_s(t_h)) / (T - t_h): a translating discrete
profile, read off its samples, wobbles by a fraction of a cell as its phase against the grid
changes. In a scan over dt/dx the endpoint difference was off by up to 0.2 cells over the window
for Engquist-Osher and Rusanov and 0.7 cells for Lax-Friedrichs; the slope by at most 0.015 and
0.33 (0.07 at N = 800). The endpoint difference is exact only when the window moves the
profile by a whole number of cells, as in the spec cases where s*T/2 = 1/4.

For a conservative scheme a translating profile must move at exactly s: the total between the
far fields grows at f(uL) - f(uR), and a translating profile's grows at s*(uL - uR). So a correct
late-window speed is a consequence of conservation, not independent evidence, and it is only a
necessary condition: a non-conservative scheme can get the speed right for one state pair by
accident. We also report the integral estimator x0 + (sum u dx(T) - sum u dx(0)) / (uL - uR); the
verdict ignores it, since for a conservative scheme it returns s from the boundary fluxes alone.

Verdict, with tolerance d = TOL*dx/(T - t_h) (half a cell of displacement over the window):
NOT_REFUTED when the late-window speed is within d of s at all three levels on the last two grids
and the levels agree to within d (the profile is translating rigidly); UNKNOWN if the levels
disagree; REFUTED_EMPIRICALLY when the error exceeds d at every level on the last two grids and
the level-0.5 error changed by under 10% between them (it has settled at a non-zero value);
UNKNOWN otherwise.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from ..expr import intern
from . import checks, poly as P
from .convergence import EMPIRICAL, NOT_REFUTED, REFUTED_EMPIRICALLY, UNKNOWN, _steps, ev, transmissive

TOL = 0.5
LEVELS = (0.2, 0.5, 0.8)
GRIDS = (200, 400, 800, 1600, 3200)
LABEL = ("Riemann problem on [0, 1], jump at x0, transmissive (constant-extrapolation) boundaries; "
         "shock located where u crosses uR + l*(uL - uR); late-window speed is the least-squares slope "
         "of the crossing over [T/2, T]")


def rh_speed(spec: dict, uL: Fraction, uR: Fraction) -> Fraction:
    """Rankine-Hugoniot speed from the PDE flux, exactly."""
    f = P.from_expr(checks.pde_flux(spec))
    fL, fR = P.evaluate(f, {"u": uL}), P.evaluate(f, {"u": uR})
    if fL is None or fR is None:
        raise P.Undecided("flux is not rational at uL or uR")
    return (fL - fR) / (uL - uR)


def crossing(u: np.ndarray, mid: float, dx: float) -> tuple[float, int]:
    """Interpolated position where u crosses mid (the steepest crossing) and the number of crossings."""
    above = u > mid
    idx = np.nonzero(above[:-1] != above[1:])[0]
    if len(idx) == 0:
        return float("nan"), 0
    i = idx[np.argmax(np.abs(u[idx] - u[idx + 1]))]
    return float((i + 0.5) * dx + (u[i] - mid) / (u[i] - u[i + 1]) * dx), len(idx)


def run(H, uL: float, uR: float, x0: float, T: float, lam: float, n: int) -> dict:
    H, dx = intern(H), 1 / n
    assert abs(x0 * n - round(x0 * n)) < 1e-9, "x0 must be a cell interface"
    u = np.where((np.arange(n) + 0.5) * dx < x0, uL, uR)
    mid = (uL + uR) / 2
    levels = [uR + l * (uL - uR) for l in LEVELS]
    xs0, _ = crossing(u, mid, dx)
    mass0 = float(np.sum(u)) * dx
    steps, dt = _steps(T, lam * dx)
    h = round(steps / 2)
    ts, xs = [], []
    with np.errstate(all="ignore"):
        for k in range(steps + 1):
            if k >= h:
                ts.append(k * dt)
                xs.append([crossing(u, c, dx)[0] for c in levels])
            if k < steps:
                u = ev(H, transmissive(u).with_lam(dt / dx))
    ts, xs = np.array(ts), np.array(xs)
    finite = bool(np.all(np.isfinite(u)) and np.all(np.isfinite(xs)))
    late = list(np.polyfit(ts, xs, 1)[0]) if finite and len(ts) > 1 else [float("nan")] * len(LEVELS)
    _, nc = crossing(u, mid, dx)
    i = LEVELS.index(0.5)
    return {"N": n, "late": late, "window": T - h * dt, "full": (xs[-1][i] - xs0) / T,
            "endpoints": (xs[-1][i] - xs[0][i]) / (T - h * dt),
            "crossings": nc, "integral_speed": (float(np.sum(u)) * dx - mass0) / (uL - uR) / T,
            "ends": (float(u[0]), float(u[-1])), "finite": finite}


def tol(r: dict) -> float:
    return TOL / r["N"] / r["window"]


def verdict(rows: list, s: float) -> tuple[str, str]:
    (a, b) = rows[-2:]
    da, db = tol(a), tol(b)
    ea, eb = (np.array(r["late"]) - s for r in (a, b))
    if not (np.all(np.isfinite(ea)) and np.all(np.isfinite(eb))):
        return UNKNOWN, "shock not found or solution not finite"
    i = LEVELS.index(0.5)
    spread = max(np.ptp(ea), np.ptp(eb))
    agree = np.ptp(ea) <= da and np.ptp(eb) <= db
    msg = (f"late-window speed error {ea[i]:+.2e} at N = {a['N']}, {eb[i]:+.2e} at N = {b['N']} "
           f"(spread across levels {', '.join(map(str, LEVELS))} at most {spread:.1e}); "
           f"tolerance {TOL} cell over the window = {da:.1e}, {db:.1e}")
    if np.all(np.abs(ea) <= da) and np.all(np.abs(eb) <= db):
        if agree:
            return NOT_REFUTED, msg
        return UNKNOWN, msg + " (levels disagree: the profile has not settled into rigid translation)"
    if np.all(np.abs(ea) > da) and np.all(np.abs(eb) > db) and abs(eb[i] - ea[i]) < 0.1 * abs(eb[i]):
        return REFUTED_EMPIRICALLY, msg + " (settled at a non-zero value" + (
            ")" if agree else "; levels disagree, so the profile is not translating rigidly)")
    return UNKNOWN, msg + " (inconclusive)"


def study(spec: dict, grids=GRIDS) -> dict:
    c = spec["claims"]["shock_speed"]
    x0 = Fraction(c.get("x0", "1/4"))
    claim = "shock speed converges to the Rankine-Hugoniot speed on Riemann problems " + ", ".join(
        f"(uL, uR) = ({k['uL']}, {k['uR']})" for k in c["cases"])
    H = checks.update(spec)
    table, statuses, details = [], [], []
    for k in c["cases"]:
        uL, uR, T, lam = (Fraction(k[v]) for v in ("uL", "uR", "T", "lam"))
        try:
            s = rh_speed(spec, uL, uR)
        except P.Undecided as ex:
            return checks.result("shock_speed", UNKNOWN, claim, str(ex))
        rows = [run(H, float(uL), float(uR), float(x0), float(T), float(lam), n) for n in grids]
        st, d = verdict(rows, float(s))
        lost = [r["N"] for r in rows if not r["finite"] or max(abs(r["ends"][0] - float(uL)), abs(r["ends"][1] - float(uR))) > 1e-6 * float(uL - uR)]
        if lost:
            st, d = UNKNOWN, f"waves reached the boundary or blew up at N = {lost}"
        statuses.append(st)
        details.append(f"(uL, uR) = ({uL}, {uR}): {d}")
        table.append(f"uL = {uL}, uR = {uR}, x0 = {x0}, T = {T}, dt/dx = {lam}: exact s = {s} = {float(s):.4f}")
        table.append(f"{'':>6} {'[0, T], includes':>17} {'[T/2, T]':>11} {'late-window error, slope, at level':>38}")
        table.append(f"{'N':>6} {'start-up offset':>17} {'endpoints':>11} {LEVELS[0]:>12} {LEVELS[1]:>12} {LEVELS[2]:>12} "
                     f"{'spread':>9} {'tolerance':>9} {'crossings':>9} {'integral est.':>13}")
        for r in rows:
            e = np.array(r["late"]) - float(s)
            table.append(f"{r['N']:>6} {r['full'] - float(s):+17.2e} {r['endpoints'] - float(s):+11.2e} {e[0]:+12.2e} {e[1]:+12.2e} {e[2]:+12.2e} "
                         f"{np.ptp(e):9.1e} {tol(r):9.1e} {r['crossings']:>9} {r['integral_speed']:13.5f}")
    status = (REFUTED_EMPIRICALLY if REFUTED_EMPIRICALLY in statuses
              else NOT_REFUTED if all(x == NOT_REFUTED for x in statuses) else UNKNOWN)
    r = checks.result("shock_speed", status, claim, "; ".join(details),
                      {"study": LABEL + " (verdict uses the late-window crossing speed; the integral estimator "
                                        "is shown for comparison only, see physverify/schemes/shock.py)",
                       "table": table})
    r["guarantee"] = EMPIRICAL
    return r
