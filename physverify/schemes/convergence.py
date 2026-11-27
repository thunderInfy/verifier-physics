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

from ..expr import E, intern
from . import checks, poly as P

NOT_REFUTED, REFUTED_EMPIRICALLY, SUSPICIOUS, UNKNOWN = "NOT_REFUTED", "REFUTED_EMPIRICALLY", "SUSPICIOUS", "UNKNOWN"
EMPIRICAL = "empirical (float64 refinement study; not a proof)"
TOL = 0.2
GRIDS = (25, 50, 100, 200, 400)
_F = {"sin": np.sin, "cos": np.cos, "exp": np.exp, "log": np.log}
_OPS = {"neg", "add", "sub", "mul", "div", "powi", "rpow", "sqrt", "app"}


def ev(e: E, env: dict, memo: dict | None = None):
    """e on numpy arrays. Memoized by node identity within one call, so on an `intern`ed e each
    distinct subexpression is evaluated once (the values are the same either way)."""
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return float(e.q)
    if k == "pi": return math.pi
    if k not in _OPS: raise ValueError(k)
    memo = {} if memo is None else memo
    if id(e) in memo:
        return memo[id(e)][1]
    x = ev(a[0], env, memo)
    if k == "neg": out = -x
    elif k == "add": out = x + ev(a[1], env, memo)
    elif k == "sub": out = x - ev(a[1], env, memo)
    elif k == "mul": out = x * ev(a[1], env, memo)
    elif k == "div": out = x / ev(a[1], env, memo)
    elif k in ("powi", "rpow"): out = x ** float(e.q)
    elif k == "sqrt": out = np.sqrt(x)
    else: out = _F[e.name](x)
    memo[id(e)] = (e, out)
    return out


_INFIX = {"add": "+", "sub": "-", "mul": "*", "div": "/"}


def evaluator(e: E):
    """`lambda env: ev(e, env)`, compiled once: a straight-line function with one line per distinct
    subexpression of e, doing the same numpy operations on the same operands as ev (so the same values,
    bit for bit) without the per-node recursion. Studies call it once per time step. Expressions ev
    would reject fall back to ev itself, so they fail exactly as before."""
    e = intern(e)
    order, index = [], {}

    def visit(x):
        if id(x) not in index:
            for y in x.args:
                visit(y)
            index[id(x)] = len(order)
            order.append(x)
    visit(e)
    if any(x.kind not in _OPS | {"var", "lit", "pi"} or x.kind == "app" and x.name not in _F for x in order):
        return lambda env: ev(e, env)
    consts, lines = [], []
    for i, x in enumerate(order):
        k, a = x.kind, [f"t{index[id(y)]}" for y in x.args]
        if k in ("lit", "powi", "rpow"):
            consts.append(float(x.q))
        rhs = (f"env[{x.name!r}]" if k == "var" else f"c[{len(consts) - 1}]" if k == "lit" else "pi" if k == "pi"
               else f"-{a[0]}" if k == "neg" else f"{a[0]} {_INFIX[k]} {a[1]}" if k in _INFIX
               else f"{a[0]} ** c[{len(consts) - 1}]" if k in ("powi", "rpow")
               else f"sqrt({a[0]})" if k == "sqrt" else f"F[{x.name!r}]({a[0]})")
        lines.append(f"    t{i} = {rhs}\n")
    ns = {"c": consts, "pi": math.pi, "sqrt": np.sqrt, "F": _F}
    exec("def f(env):\n" + "".join(lines) + f"    return t{len(order) - 1}\n", ns)
    return ns["f"]


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
    if problem["kind"] == "advection-smooth-step":
        # a C-infinity monotone step from 0 to amp on [x1, x2], constant outside: no extrema, and with
        # transmissive boundaries the constant ends are exact as long as the step stays inside [0, 1]
        x1, x2 = problem.get("x1", 0.2), problem.get("x2", 0.6)
        s = np.clip((x - problem["speed"] * t - x1) / (x2 - x1), 0.0, 1.0)
        with np.errstate(divide="ignore"):
            f = lambda y: np.where(y > 0, np.exp(-1.0 / np.where(y > 0, y, 1.0)), 0.0)
            return amp * f(s) / (f(s) + f(1 - s))
    raise ValueError(problem["kind"])


class _Neighbours(dict):
    """{um2: u_{i-2}, ..., up2: u_{i+2}} as arrays, each built only when the update uses it."""

    def __init__(self, shift):
        super().__init__()
        self.shift = shift

    def with_lam(self, lam):
        self["lam"] = lam
        return self

    def __missing__(self, name):
        if name not in checks.OFFSET5:
            raise KeyError(name)
        self[name] = self.shift(checks.OFFSET5[name])
        return self[name]


def periodic(u) -> dict:
    """The neighbours u_{i+k}, k = -2..2, on a periodic grid."""
    return _Neighbours(lambda k: np.roll(u, -k) if k else u)


def transmissive(u) -> dict:
    """The neighbours u_{i+k}, k = -2..2, with constant extrapolation past both ends."""
    pad = np.concatenate(([u[0]] * 2, u, [u[-1]] * 2))
    return _Neighbours(lambda k: pad[2 + k: len(pad) - 2 + k])


def _stencil(f, u, lam):
    return f(periodic(u).with_lam(lam))


def _grid(n):
    return np.arange(n) / n


def _errors(u, ref, dx):
    d = np.abs(u - ref)
    return float(np.sum(d) * dx), float(np.max(d))


def _rk4(f, u, dx, dt, steps):
    rhs = lambda v: (_stencil(f, v, 1.0) - v) / dx
    for _ in range(steps):
        k1 = rhs(u); k2 = rhs(u + dt / 2 * k1); k3 = rhs(u + dt / 2 * k2); k4 = rhs(u + dt * k3)
        u = u + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return u


def _steps(T, dt):
    n = max(1, math.ceil(T / dt - 1e-9))
    return n, T / n


def combined(H: E, problem: dict, T: float, lam: float, boundary: str = "periodic", grids=GRIDS) -> list:
    f, rows = evaluator(H), []
    for n in grids:
        x, dx = _grid(n), 1 / n
        steps, dt = _steps(T, lam * dx)
        u = exact(problem, x, 0)
        for _ in range(steps):
            if boundary == "periodic":
                u = _stencil(f, u, dt / dx)
            else:
                u = f(transmissive(u).with_lam(dt / dx))
        rows.append((n, *_errors(u, exact(problem, x, T), dx)))
    return rows


def space(H: E, problem: dict, T: float) -> list:
    f, rows = evaluator(H), []
    for n in GRIDS:
        x, dx = _grid(n), 1 / n
        steps, dt = _steps(T, 0.2 * dx)
        rows.append((n, *_errors(_rk4(f, exact(problem, x, 0), dx, dt, steps), exact(problem, x, T), dx)))
    return rows


def time(H: E, problem: dict, T: float, n: int = 200) -> list:
    f = evaluator(H)
    x, dx = _grid(n), 1 / n
    steps, dt = _steps(T, dx / 20)
    ref = _rk4(f, exact(problem, x, 0), dx, dt, steps)
    rows = []
    for nu in (0.8, 0.4, 0.2, 0.1, 0.05):
        steps, dt = _steps(T, nu * dx)
        u = exact(problem, x, 0)
        for _ in range(steps):
            u = u + dt * (_stencil(f, u, 1.0) - u) / dx
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


def verdict(rows: list, p: float, norm: int | None = None) -> tuple[str, str]:
    """norm None: L1 and Linf together (the original studies); 0: L1 only; 1: Linf only."""
    last = [q for pair in orders(rows)[-2:] for i, q in enumerate(pair) if norm is None or i == norm]
    if any(math.isnan(q) for q in last):
        return UNKNOWN, "error vanished or is not finite"
    lo, hi = min(last), max(last)
    which = "" if norm is None else f" ({NORMS[norm]} only)"
    rng = f"observed orders{which} over the last two refinements in [{lo:.2f}, {hi:.2f}], claimed {p}, tolerance {TOL}"
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


NORMS = ("L1", "Linf")
NORM_KEYS = {"order_l1": 0, "order_linf": 1}          # claims.order_l1 = {"combined": p}: one norm only


def studies(spec: dict) -> list[dict]:
    out = _studies(spec)
    test = spec["test"]
    boundary, grids = test.get("boundary", "periodic"), tuple(test.get("grids", GRIDS))
    rows = None
    for key, norm in NORM_KEYS.items():
        claimed = spec.get("claims", {}).get(key, {})
        for kind, p in claimed.items():
            claim = f"combined order {p} in the {NORMS[norm]} norm on {test['problem']['kind']} to T = {test['T']}"
            if kind != "combined":
                out.append(checks.result(f"{key}/{kind}", UNKNOWN, claim, "per-norm claims cover the combined study only"))
                continue
            if rows is None:
                rows = combined(checks.update(spec), test["problem"], test["T"], test["lam"], boundary, grids)
            status, detail = verdict(rows, p, norm)
            label = (f"combined: fully discrete scheme at fixed dt/dx = {test['lam']}, refining dx and dt together, "
                     f"{boundary} boundaries; verdict on the {NORMS[norm]} column only")
            r = checks.result(f"{key}/{kind}", status, claim, detail, {"study": label, "table": table(rows, "N")})
            r["guarantee"] = EMPIRICAL
            out.append(r)
    return out


def _studies(spec: dict) -> list[dict]:
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
        rows = (combined(H, test["problem"], test["T"], test["lam"], test.get("boundary", "periodic"),
                         tuple(test.get("grids", GRIDS))) if kind == "combined"
                else space(H, test["problem"], test["T"]) if kind == "space" else time(H, test["problem"], test["T"]))
        status, detail = verdict(rows, p)
        r = checks.result(f"order/{kind}", status, claim, detail,
                          {"study": label, "table": table(rows, "N" if kind != "time" else "steps")})
        r["guarantee"] = EMPIRICAL
        out.append(r)
    return out
