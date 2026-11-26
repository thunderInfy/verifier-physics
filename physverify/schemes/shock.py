"""Riemann-problem shock-speed study (numpy floats; evidence, not proof).

For data uL > uR on [0, 1] with the jump at x0 (a cell interface), the entropy solution of a
convex law such as Burgers is a single shock moving at the Rankine-Hugoniot speed
s = (f(uL) - f(uR)) / (uL - uR), computed here from the spec's PDE flux in Fraction arithmetic.
The scheme runs at fixed dt/dx on a non-periodic grid with transmissive (constant-extrapolation)
ghost cells; the claim's T is chosen so the shock stays inside the domain, and the study is
UNKNOWN if the end cells drift from uL or uR by more than 1e-6*(uL - uR).

The shock position is read off the profile: where u crosses (uL + uR)/2, interpolated linearly
between the two cells. The measured speed is (x_s(T) - x_s(0)) / T. We also report the integral
estimator x0 + (sum u dx(T) - sum u dx(0)) / (uL - uR), but it is not used for the verdict: for a
conservative scheme the total changes by exactly T*(f(uL) - f(uR)) through the boundary fluxes,
so it returns s whatever the profile looks like, and for a non-conservative scheme it only means
something if the profile is a single uL | uR step.

Verdict, with grid-scale uncertainty d = K*dx/T (K = 4): NOT_REFUTED when |speed error| <= d on
the last two grids (the error shrinks at least like dx); REFUTED_EMPIRICALLY when |error| > d on
the last two grids and it changed by at most d between them (it has settled at a non-zero
value); UNKNOWN otherwise.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from . import checks, poly as P
from .convergence import EMPIRICAL, NOT_REFUTED, REFUTED_EMPIRICALLY, UNKNOWN, _steps, ev

K = 4
GRIDS = (200, 400, 800, 1600, 3200)
LABEL = ("Riemann problem on [0, 1], jump at x0, transmissive (constant-extrapolation) boundaries; "
         "shock located where u crosses (uL + uR)/2")


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
    dx = 1 / n
    assert abs(x0 * n - round(x0 * n)) < 1e-9, "x0 must be a cell interface"
    u = np.where((np.arange(n) + 0.5) * dx < x0, uL, uR)
    mid = (uL + uR) / 2
    xs0, _ = crossing(u, mid, dx)
    mass0 = float(np.sum(u)) * dx
    steps, dt = _steps(T, lam * dx)
    with np.errstate(all="ignore"):
        for _ in range(steps):
            u = ev(H, {"um1": np.concatenate(([u[0]], u[:-1])), "u0": u,
                       "up1": np.concatenate((u[1:], [u[-1]])), "lam": dt / dx})
    xs, nc = crossing(u, mid, dx)
    return {"N": n, "speed": (xs - xs0) / T, "crossings": nc,
            "integral_speed": (float(np.sum(u)) * dx - mass0) / (uL - uR) / T,
            "ends": (float(u[0]), float(u[-1])), "finite": bool(np.all(np.isfinite(u)))}


def verdict(rows: list, s: float, T: float) -> tuple[str, str]:
    (a, b) = rows[-2:]
    da, db = K / a["N"] / T, K / b["N"] / T
    ea, eb = a["speed"] - s, b["speed"] - s
    if not (np.isfinite(ea) and np.isfinite(eb)):
        return UNKNOWN, "shock not found or solution not finite"
    msg = f"speed error {ea:+.2e} at N = {a['N']}, {eb:+.2e} at N = {b['N']}; grid-scale tolerance {K}*dx/T = {da:.4f}, {db:.4f}"
    if abs(ea) <= da and abs(eb) <= db:
        return NOT_REFUTED, msg
    if abs(ea) > da and abs(eb) > db and abs(eb - ea) <= da:
        return REFUTED_EMPIRICALLY, msg + " (settled at a non-zero value)"
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
        st, d = verdict(rows, float(s), float(T))
        lost = [r["N"] for r in rows if not r["finite"] or max(abs(r["ends"][0] - float(uL)), abs(r["ends"][1] - float(uR))) > 1e-6 * float(uL - uR)]
        if lost:
            st, d = UNKNOWN, f"waves reached the boundary or blew up at N = {lost}"
        statuses.append(st)
        details.append(f"(uL, uR) = ({uL}, {uR}): {d}")
        table.append(f"uL = {uL}, uR = {uR}, x0 = {x0}, T = {T}, dt/dx = {lam}: exact s = {s} = {float(s):.4f}")
        table.append(f"{'N':>6} {'speed':>8} {'error':>10} {'4dx/T':>7} {'crossings':>9} {'integral est.':>13}")
        for r in rows:
            table.append(f"{r['N']:>6} {r['speed']:8.5f} {r['speed'] - float(s):+10.2e} {K / r['N'] / float(T):7.4f} "
                         f"{r['crossings']:>9} {r['integral_speed']:13.5f}")
    status = (REFUTED_EMPIRICALLY if REFUTED_EMPIRICALLY in statuses
              else NOT_REFUTED if all(x == NOT_REFUTED for x in statuses) else UNKNOWN)
    r = checks.result("shock_speed", status, claim, "; ".join(details),
                      {"study": LABEL + " (verdict uses the crossing; the integral estimator is shown for "
                                        "comparison only, see physverify/schemes/shock.py)", "table": table})
    r["guarantee"] = EMPIRICAL
    return r
