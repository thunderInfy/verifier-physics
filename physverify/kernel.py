"""Straight-line kernels: one time step written once as a list of assignments, run by Lean's
`exec` (`lean/PhysVerify/Kernel.lean`) and printed as C (`physverify/kernel_c.py`).

Claim file (`benchmark/kernels/*.json`):
{
  "kind": "kernel", "name": "...",
  "state": ["q", "p"],                              # z; Lean index k for the k-th entry
  "symbols": {"q": {"dim": "L"}, "p": {...}, "h": {"dim": "T"}, "w": {...}},
  "program": [{"set": "p", "to": "p - h*w^2*q"},    # run in order: each assignment reads the
              {"set": "q", "to": "q + h*p"}],       # values the previous ones wrote
  "domain": ["w > 0"],                              # atoms over z, h, parameters; h > 0 added
  "claims": [...]                                   # as for "update_map" (variational.py)
}

An assignment writes a state variable or a temporary (any name not in `symbols`); it may not
write `h` or a parameter. A temporary must be assigned before it is read; its dimension is that
of its first assignment. The domain and the claimed quantities may not mention temporaries.
Lean layout: state 0..n-1, then `h` and the parameters (sorted), then the temporaries in
order of first assignment.

What changes against `update_map`: Lean sees the program, node for node, and its meaning is
`exec` (sequential assignment), so the composition of sub-steps is no longer trusted Python.
`compose` (the old substitution) is kept for two things only: the exact order claims
(`update_conserves_order_p`, exact Python on the composed map, as before) and a cross-check
against `exec` in the tests.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import ClassVar

from . import units
from .expr import E, parse, substitute, to_lean, var, variables
from .theory import Malformed
from .variational import (UPDATE_KINDS, UpdateMap, VClaim, _check_domain, _parse_domain, update_terms)

KERNEL_MODULE = "PhysVerify.Kernel"


@dataclass
class Kernel(UpdateMap):
    program: list[tuple[str, E]] = field(default_factory=list)
    temps: list[str] = field(default_factory=list)
    dim_errors: list[str] = field(default_factory=list)

    MODULE: ClassVar[str] = KERNEL_MODULE

    def index(self) -> dict[str, int]:
        idx = super().index()
        idx.update({t: len(idx) + i for i, t in enumerate(self.temps)})
        return idx

    def lean_prog(self) -> str:
        idx = self.index()
        return "([" + ", ".join(f"({idx[x]}, {to_lean(e, idx)})" for x, e in self.program) + "] : Prog)"

    def lean_statement(self, kind: str, c: VClaim) -> str:
        t = update_terms(self, c)
        P = self.lean_prog()
        if kind == "verified":
            return (f"(Expr.dimOf {t['ctx']} {t['J']}).isSome = true ∧ ProgDims {t['ctx']} {P} = true ∧ "
                    f"KernelVerified {P} {t['D']} {t['J']}")
        if kind == "refuted":
            return f"KernelRefuted {P} {t['D']} {t['J']}"
        raise KeyError((kind, c.kind))

    def verified_prefix(self, point: str) -> str:
        return (f"refine ⟨by decide, by decide, ⟨{point}, ?_⟩, ?_⟩\n"
                "· first | trivial | (simp [Expr.eval, Fn.eval] <;> norm_num)\n")

    def dims_check(self, c: VClaim) -> str:
        """Python mirror of `ProgDims` and of the `dimOf` check of J."""
        if self.dim_errors:
            return f"mismatch: {self.dim_errors[0]}"
        try:
            units.dim_of(c.quantity, self.dims)
            for x, e in self.program:
                d = units.dim_of(e, self.dims)
                if d != self.dims[x]:
                    return f"mismatch: {x} := … has {units.fmt_dim(d)}, {x} has {units.fmt_dim(self.dims[x])}"
        except units.DimError as ex:
            return f"mismatch: {ex}"
        return "ok"

    MEANING: ClassVar[dict] = {
        ("update_conserves", "VERIFIED"): (
            "PhysVerify.kernel_conserves_meaning: along every orbit z_k+1 = exec prog z_k of the "
            "straight-line program (assignments run in order) whose points z_0..z_N-1 are in the "
            "domain, J(z_N) = J(z_0) exactly; the domain is non-empty, every assignment is junk-free "
            "where it runs, and J is junk-free before and after the step"),
        ("update_conserves", "REFUTED"): (
            "PhysVerify.kernel_refuted_meaning: a rational point z_0 in the domain whose orbit under "
            "exec prog has J(z_1) ≠ J(z_0), with no junk value in any assignment of the first step"),
    }


def is_kernel(spec: dict) -> bool:
    return spec.get("kind") == "kernel"


def compose(state: list[str], program: list[tuple[str, E]]) -> list[E]:
    """Φ_k by substitution: the composed simultaneous map (a cross-check of `exec` only)."""
    cur = {z: var(z) for z in state}
    for x, e in program:
        cur[x] = substitute(e, cur)
    return [cur[z] for z in state]


def load_kernel(spec: dict | str | Path) -> Kernel:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    if not is_kernel(spec):
        raise Malformed(f"claim {spec.get('name')!r}: not a kernel claim")
    name = spec.get("name")
    try:
        state = list(spec["state"])
        declared = dict(spec["symbols"])
        declared.setdefault("h", {"dim": "T"})
        dims = {k: units.parse_dim(v["dim"]) for k, v in declared.items()}
        if dims["h"] != units.parse_dim("T"):
            raise Malformed("the step h must have dimension T")
        for z in state:
            if z not in dims:
                raise Malformed(f"state variable {z!r} has no dimension")
        params = set(declared) - set(state)
        program, temps, errs = [], [], []
        for i, st in enumerate(spec["program"]):
            if set(st) != {"set", "to"}:
                raise Malformed(f"assignment {i} must have exactly the keys 'set' and 'to'")
            x, e = st["set"], parse(st["to"])
            bad = variables(e) - set(declared) - set(temps)
            if bad:
                raise Malformed(f"assignment {i} ({x} := …) reads {sorted(bad)}, which are not "
                                "symbols or temporaries assigned before it")
            if x in params:
                raise Malformed(f"assignment {i} writes {x!r}, which is h or a parameter")
            if x not in declared and x not in temps:
                temps.append(x)
                try:
                    dims[x] = units.dim_of(e, dims)
                except units.DimError as ex:
                    dims[x] = units.ZERO
                    errs.append(f"temporary {x}: {ex}")
            program.append((x, e))
        if not program:
            raise Malformed("the program is empty")
        dom = _parse_domain(spec)
        claims = []
        for c in spec["claims"]:
            kind = c["claim"]
            if kind not in UPDATE_KINDS:
                raise Malformed(f"unknown claim kind {kind!r} (use {UPDATE_KINDS})")
            vc = VClaim(kind, c.get("expect", ""), c.get("why", ""), quantity=parse(c["quantity"]))
            if kind == "update_conserves_order_p":
                vc.p = int(c["p"])
            claims.append(vc)
    except (KeyError, ValueError, TypeError, AttributeError) as ex:
        raise Malformed(f"claim {name!r}: {ex}") from ex
    allowed = set(declared)
    _check_domain(name, dom, allowed)
    for c in claims:
        bad = variables(c.quantity) - allowed
        if bad:
            raise Malformed(f"claim {name!r}: the quantity may not mention {sorted(bad)}")
        if c.kind == "update_conserves_order_p" and c.p < 1:
            raise Malformed(f"claim {name!r}: the order p must be at least 1")
    return Kernel(name, state, dims, sorted(declared), compose(state, program), dom, claims, spec,
                  program, temps, errs)


# ---------------------------------------------------------------- exact and float evaluation

class Junk(ValueError):
    """A value Lean would totalise (x/0, a negative power of 0, sqrt of a negative) or one
    that is not rational (sqrt of a non-square, π, transcendental functions)."""


def _isqrt_q(x: Fraction) -> Fraction:
    import math
    if x < 0:
        raise Junk("sqrt of a negative number")
    n, d = math.isqrt(x.numerator), math.isqrt(x.denominator)
    if n * n != x.numerator or d * d != x.denominator:
        raise Junk("sqrt of a non-square rational")
    return Fraction(n, d)


def qvalue(e: E, env: dict[str, Fraction]) -> Fraction:
    """Exact rational value of `e`; raises `Junk` where `physOK` fails or the value is not
    rational."""
    k, a = e.kind, e.args
    if k == "var": return Fraction(env[e.name])
    if k == "lit": return Fraction(e.q)
    xs = [qvalue(x, env) for x in a]
    if k == "neg": return -xs[0]
    if k == "add": return xs[0] + xs[1]
    if k == "sub": return xs[0] - xs[1]
    if k == "mul": return xs[0] * xs[1]
    if k == "div":
        if xs[1] == 0:
            raise Junk("division by zero")
        return xs[0] / xs[1]
    if k == "powi":
        if xs[0] == 0 and e.q < 0:
            raise Junk("negative power of zero")
        return xs[0] ** int(e.q)
    if k == "sqrt":
        if xs[0] == 0:
            raise Junk("sqrt of zero (physOK needs a positive argument)")
        return _isqrt_q(xs[0])
    raise Junk(f"{k} has no exact rational value here")


def run(program: list[tuple[str, E]], env: dict[str, Fraction]) -> dict[str, Fraction]:
    """One step, exactly: the Python mirror of Lean's `exec` (and of `ExecOK`, via `Junk`)."""
    cur = dict(env)
    for x, e in program:
        cur[x] = qvalue(e, cur)
    return cur


def fvalue(e: E, env: dict[str, float]) -> float:
    """Double-precision value, the same operations in the same order as `kernel_c` prints."""
    import math
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return float(e.q.numerator) / float(e.q.denominator)
    if k == "pi": return math.pi
    xs = [fvalue(x, env) for x in a]
    if k == "neg": return -xs[0]
    if k == "add": return xs[0] + xs[1]
    if k == "sub": return xs[0] - xs[1]
    if k == "mul": return xs[0] * xs[1]
    if k == "div": return xs[0] / xs[1]
    if k == "powi":
        r = 1.0
        for _ in range(abs(int(e.q))):
            r = r * xs[0]
        return r if e.q >= 0 else 1.0 / r
    if k == "sqrt": return math.sqrt(xs[0])
    raise ValueError(f"{k}: no float evaluation in v1")


def run_float(program: list[tuple[str, E]], env: dict[str, float]) -> dict[str, float]:
    cur = dict(env)
    for x, e in program:
        cur[x] = fvalue(e, cur)
    return cur
