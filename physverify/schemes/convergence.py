"""Empirical convergence-order studies (numpy floats; evidence, not proof).

Three studies, each labelled in its output:
- combined: the fully discrete scheme at fixed lam = dt/dx, refining dx and dt together;
- space: method of lines du_i/dt = (H - u_i)|_{lam=1} / dx with classical RK4 at dt = 0.2*dx
  (time error O(dt^4) is far below the spatial error), refining dx; needs H - u0 to be
  exactly lam times something lam-free;
- time: forward Euler on a fixed grid (N = 200), refining dt, measured against the
  same-grid semi-discrete solution from RK4 at dt = dx/20. The spatial error is identical
  in both and cancels, so only the time error is measured.

A claimed order p is NOT_REFUTED when the observed orders of the last two refinements in
both L1 and Linf lie within TOL of p, REFUTED_EMPIRICALLY when one is below p - TOL, and
SUSPICIOUS when one is above p + TOL (superconvergence on this test is not a pass).
"""

from __future__ import annotations

import math

import numpy as np

from ..expr import E
from . import checks, poly as P

NOT_REFUTED, REFUTED_EMPIRICALLY, SUSPICIOUS, UNKNOWN = "NOT_REFUTED", "REFUTED_EMPIRICALLY", "SUSPICIOUS", "UNKNOWN"
EMPIRICAL = "empirical (float64 refinement study; not a proof)"
TOL = 0.2
GRIDS = (25, 50, 100, 200, 400)
_F = {"sin": np.sin, "cos": np.cos, "exp": np.exp, "log": np.log}


def ev(e: E, env: dict):
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return float(e.q)
    if k == "pi": return math.pi
    if k == "neg": return -ev(a[0], env)
    if k in ("add", "sub", "mul", "div"):
        x, y = ev(a[0], env), ev(a[1], env)
        return {"add": x + y, "sub": x - y, "mul": x * y}[k] if k != "div" else x / y
    if k in ("powi", "rpow"): return ev(a[0], env) ** float(e.q)
    if k == "sqrt": return np.sqrt(ev(a[0], env))
    if k == "app": return _F[e.name](ev(a[0], env))
    raise ValueError(k)


def exact(problem: dict, x: np.ndarray, t: float) -> np.ndarray:
    """Exact solutions on the periodic unit interval."""
    amp = problem.get("amplitude", 1.0)
    if problem["kind"] == "advection-sine":
        return amp * np.sin(2 * np.pi * (x - problem["speed"] * t))
    if problem["kind"] == "burgers-sine":
        # characteristics: u = g(x - u t), g = mean + amp*sin(2 pi .); smooth while
        # t < 1/(2 pi amp). Newton on the implicit equation until the residual is at round-off.
        mean = problem.get("mean", 0.0)
        assert t * 2 * np.pi * amp < 1, "Burgers exact solution requested after shock formation"
        u = mean + amp * np.sin(2 * np.pi * x)
        for _ in range(100):
            xi = x - u * t
            r = u - mean - amp * np.sin(2 * np.pi * xi)
            u = u - r / (1 + 2 * np.pi * amp * t * np.cos(2 * np.pi * xi))
            if np.max(np.abs(r)) < 1e-15:
                break
        return u
    raise ValueError(problem["kind"])


def _stencil(H: E, u, lam):
    return ev(H, {"um1": np.roll(u, 1), "u0": u, "up1": np.roll(u, -1), "lam": lam})


def _grid(n):
    return np.arange(n) / n


def _errors(u, ref, dx):
    d = np.abs(u - ref)
    return float(np.sum(d) * dx), float(np.max(d))


def _rk4(H: E, u, dx, dt, steps):
    rhs = lambda v: (_stencil(H, v, 1.0) - v) / dx
    for _ in range(steps):
        k1 = rhs(u); k2 = rhs(u + dt / 2 * k1); k3 = rhs(u + dt / 2 * k2); k4 = rhs(u + dt * k3)
        u = u + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return u


def _steps(T, dt):
    n = max(1, math.ceil(T / dt - 1e-9))
    return n, T / n


def combined(H: E, problem: dict, T: float, lam: float) -> list:
    rows = []
    for n in GRIDS:
        x, dx = _grid(n), 1 / n
        steps, dt = _steps(T, lam * dx)
        u = exact(problem, x, 0)
        for _ in range(steps):
            u = _stencil(H, u, dt / dx)
        rows.append((n, *_errors(u, exact(problem, x, T), dx)))
    return rows


def space(H: E, problem: dict, T: float) -> list:
    rows = []
    for n in GRIDS:
        x, dx = _grid(n), 1 / n
        steps, dt = _steps(T, 0.2 * dx)
        rows.append((n, *_errors(_rk4(H, exact(problem, x, 0), dx, dt, steps), exact(problem, x, T), dx)))
    return rows


def time(H: E, problem: dict, T: float, n: int = 200) -> list:
    x, dx = _grid(n), 1 / n
    steps, dt = _steps(T, dx / 20)
    ref = _rk4(H, exact(problem, x, 0), dx, dt, steps)
    rows = []
    for nu in (0.8, 0.4, 0.2, 0.1, 0.05):
        steps, dt = _steps(T, nu * dx)
        u = exact(problem, x, 0)
        for _ in range(steps):
            u = u + dt * (_stencil(H, u, 1.0) - u) / dx
        rows.append((steps, *_errors(u, ref, dx)))
    return rows


def orders(rows: list) -> list:
    """Observed orders between successive rows (refinement factor from the first column)."""
    out = []
    for (n0, a0, b0), (n1, a1, b1) in zip(rows, rows[1:]):
        r = math.log(n1 / n0)
        out.append(tuple(math.log(e0 / e1) / r if e0 > 0 and e1 > 0 else float("nan")
                         for e0, e1 in ((a0, a1), (b0, b1))))
    return out


def verdict(rows: list, p: float) -> tuple[str, str]:
    last = [q for pair in orders(rows)[-2:] for q in pair]
    if any(math.isnan(q) for q in last):
        return UNKNOWN, "error vanished or is not finite"
    lo, hi = min(last), max(last)
    rng = f"observed orders over the last two refinements in [{lo:.2f}, {hi:.2f}], claimed {p}, tolerance {TOL}"
    if lo < p - TOL:
        return REFUTED_EMPIRICALLY, rng
    if hi > p + TOL:
        return SUSPICIOUS, rng + " (superconvergence on this test: suspicious, not a pass)"
    return NOT_REFUTED, rng


def table(rows: list, label: str) -> list[str]:
    out = [f"{label:>6} {'L1 error':>11} {'order':>6} {'Linf error':>11} {'order':>6}"]
    ords = [(float("nan"), float("nan"))] + orders(rows)
    for (n, a, b), (pa, pb) in zip(rows, ords):
        f = lambda q: "" if math.isnan(q) else f"{q:.2f}"
        out.append(f"{n:>6} {a:11.3e} {f(pa):>6} {b:11.3e} {f(pb):>6}")
    return out


def _mol_ok(H: E) -> tuple[bool, str]:
    """Method of lines needs H - u0 = lam * R with R free of lam."""
    try:
        D = P.add(P.from_expr(H), P.var("u0"), -1)
    except P.Undecided as ex:
        return False, str(ex)
    if all(dict(m).get(("v", "lam"), 0) == 1 for m in D):
        return True, ""
    return False, "the update is not linear in dt/dx (the flux depends on dt/dx), so space and time do not separate"


def studies(spec: dict) -> list[dict]:
    claimed = spec.get("claims", {}).get("order", {})
    test = spec["test"]
    H = checks.update(spec)
    runs = {"combined": f"combined: fully discrete scheme at fixed dt/dx = {test['lam']}, refining dx and dt together",
            "space": "space: method of lines, RK4 at dt = 0.2*dx (time error negligible), refining dx",
            "time": "time: forward Euler on fixed N = 200, refining dt, against the same-grid RK4 solution at dt = dx/20"}
    out = []
    for kind, label in runs.items():
        if kind not in claimed:
            continue
        p = claimed[kind]
        claim = f"{kind} order {p} on {test['problem']['kind']} to T = {test['T']}"
        if kind != "combined":
            ok, why = _mol_ok(H)
            if not ok:
                out.append(checks.result(f"order/{kind}", UNKNOWN, claim, why))
                continue
        rows = (combined(H, test["problem"], test["T"], test["lam"]) if kind == "combined"
                else space(H, test["problem"], test["T"]) if kind == "space" else time(H, test["problem"], test["T"]))
        status, detail = verdict(rows, p)
        r = checks.result(f"order/{kind}", status, claim, detail,
                          {"study": label, "table": table(rows, "N" if kind != "time" else "steps")})
        r["guarantee"] = EMPIRICAL
        out.append(r)
    return out
