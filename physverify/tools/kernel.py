"""Untrusted proof search for `update_conserves` on straight-line kernels
(`physverify/kernel.py`, `PhysVerify/Kernel.lean`).

Routing is the same exact decision as for explicit maps (the rational normal form of
J(Φ(z)) − J(z) on the composed map). The tactics differ: they unfold `exec` and `ExecOK`, so
Lean evaluates the assignments in order, and junk-freeness is proved step by step. A
refutation point must make every assignment junk-free where it runs (checked exactly with
`kernel.run`), not only the composed map.
"""

from __future__ import annotations

import random
from fractions import Fraction

from ..expr import to_lean, variables
from ..kernel import Junk, Kernel, qvalue, run
from ..variational import VClaim
from .eulerlagrange import NONZERO, _denominators, _env_lean
from .variational import CLOSE, IDENT, PHYS1, _intro, _sign_close, update_points

EXEC = "exec, ExecOK, Function.update_apply"


def kernel_point_ok(K: Kernel, c: VClaim, env: dict) -> dict | None:
    """The environment after the step if `env` is in D and every assignment, and J before and
    after, are junk-free (exactly); else None."""
    try:
        for op, a, b in K.domain:
            x, y = qvalue(a, env), qvalue(b, env)
            if not {">": x > y, "<": x < y, "!=": x != y}[op]:
                return None
        qvalue(c.quantity, env)
        after = run(K.program, env)
        qvalue(c.quantity, after)
    except Junk:
        return None
    return after


def kernel_refutation_point(K: Kernel, c: VClaim, seed: int = 0) -> dict | None:
    """A rational z ∈ D (h > 0, temporaries 0) with J(exec z) ≠ J(z), exactly."""
    rng = random.Random(seed)
    for env in update_points(K, rng, 200):
        env.update({t: Fraction(0) for t in K.temps})
        after = kernel_point_ok(K, c, env)
        if after is not None and qvalue(c.quantity, after) != qvalue(c.quantity, env):
            return env
    return None


def kernel_verified_tactic(K: Kernel, c: VClaim) -> str:
    idx = K.index()
    intro, facts, hyps = _intro(K)
    close = f"{CLOSE} | {_sign_close(K)}"
    dens, seen = [], set()
    for e in [*K.phi, *(e for _, e in K.program), c.quantity]:
        for d in _denominators(e):
            if repr(d) not in seen and not (d.kind == "lit" or d.kind == "var") and \
                    not (variables(d) & set(K.temps)):
                seen.add(repr(d))
                dens.append(d)
    haves = "".join(
        f"\nhave hden{i} : Expr.eval env {to_lean(d, idx)} ≠ 0 := by\n"
        f"  simp [Expr.eval, Fn.eval, {NONZERO}{hyps}] <;> {close}\n"
        f"simp [Expr.eval, Fn.eval] at hden{i}" for i, d in enumerate(dens))
    dh = "".join(f", hden{i}" for i in range(len(dens)))
    return f"""{intro}{haves}
refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
· simp [{EXEC}, {PHYS1}, {NONZERO}{hyps}{dh}] <;> {close}
· simp [{PHYS1}, {NONZERO}{hyps}] <;> {close}
· simp [{EXEC}, {PHYS1}, {NONZERO}{hyps}{dh}] <;> {close}
· simp [{EXEC}, Expr.eval, Fn.eval{facts}] <;> {IDENT}"""


def kernel_refuted_tactic(K: Kernel, w: dict) -> str:
    return f"""refine ⟨{_env_lean(K, w)}, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
· simp [Expr.eval] <;> norm_num
· simp [{EXEC}, {PHYS1}] <;> norm_num
· simp [{PHYS1}] <;> norm_num
· simp [{EXEC}, {PHYS1}] <;> norm_num
· simp [{EXEC}, Expr.eval, Fn.eval] <;> norm_num"""
