"""C emission for straight-line kernels (`physverify/kernel.py`). TRUSTED printer: nothing
proves that the C it writes means `exec`; `tests/test_kernel.py` checks it empirically
(compiled C against the exact rational evaluator, and bit for bit against `kernel.run_float`).

One C statement per assignment, in program order, so C's sequential assignment is the
program's. Layout: `z[k]` is the k-th state variable (read and written in place), `par[i]` the
i-th of `h` and the parameters (sorted, as in the Lean layout), `t_<name>` a temporary (a
local). Only + - * /, integer powers (a multiplication loop, `kp_ipow`), `sqrt` and rational
literals (`n.0 / d.0`) are printed, the operations `kernel.fvalue` mirrors one for one;
anything else raises. Compile without FMA contraction (`-std=c99`, or `-ffp-contract=off`).
"""

from __future__ import annotations

from .expr import E
from .kernel import Kernel

_EXACT = 2 ** 53          # integers up to this are exact doubles

PRELUDE = """#include <math.h>

static inline double kp_ipow(double x, int n) {
    double r = 1.0;
    int m = n < 0 ? -n : n;
    for (int i = 0; i < m; i++) r = r * x;
    return n < 0 ? 1.0 / r : r;
}
"""


def _names(K: Kernel) -> dict[str, str]:
    out = {z: f"z[{k}]" for k, z in enumerate(K.state)}
    out.update({s: f"par[{i}]" for i, s in enumerate(K.params())})
    out.update({t: f"t_{t}" for t in K.temps})
    return out


def c_expr(e: E, names: dict[str, str]) -> str:
    k, a = e.kind, e.args
    if k == "var":
        return names[e.name]
    if k == "lit":
        n, d = e.q.numerator, e.q.denominator
        if abs(n) > _EXACT or d > _EXACT:
            raise ValueError(f"literal {e.q} is not a ratio of exact doubles")
        return f"({n}.0 / {d}.0)"
    if k == "neg":
        return f"(-{c_expr(a[0], names)})"
    if k in ("add", "sub", "mul", "div"):
        op = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[k]
        return f"({c_expr(a[0], names)} {op} {c_expr(a[1], names)})"
    if k == "powi":
        return f"kp_ipow({c_expr(a[0], names)}, {int(e.q)})"
    if k == "sqrt":
        return f"sqrt({c_expr(a[0], names)})"
    raise ValueError(f"{k}: not printed to C in v1")


def emit(K: Kernel, fn: str = "step") -> str:
    """The C source of one time step: `static inline void fn(double *restrict z,
    const double *restrict par)`."""
    names = _names(K)
    lines = [f"/* {K.name}: generated from the kernel program, one statement per assignment.",
             f"   z = [{', '.join(K.state)}], par = [{', '.join(K.params())}] */",
             PRELUDE,
             f"static inline void {fn}(double *restrict z, const double *restrict par) {{"]
    if K.temps:
        lines.append("    double " + ", ".join(names[t] for t in K.temps) + ";")
    for x, e in K.program:
        lines.append(f"    {names[x]} = {c_expr(e, names)};")
    lines.append("}")
    return "\n".join(lines) + "\n"
