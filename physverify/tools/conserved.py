"""Untrusted proof search for conserved-quantity claims (`physverify/conserved.py`).

* VERIFIED: dt Q is affine in the accelerations, and so is every EL_k (with matrix H, the
  velocity Hessian of L). The multipliers λ = (∂Q/∂q̇) H⁻¹ match the q̈ coefficients of
  `dt Q = Σ λ_k EL_k`; if the remaining identity holds at random points, we emit tactics
  proving it on the domain.
* REFUTED: a jet with rational q, q̇ and parameters, q̈ solving the EL system (exactly, as
  rationals when the trig values are rational; otherwise as the symbolic solution evaluated
  in Lean), with an invertible Hessian and dt Q ≠ 0.

Nothing here is trusted: the judge only asks Lean whether the tactics prove its statement.
"""

from __future__ import annotations

import random
from fractions import Fraction

import mpmath as mp

from ..conserved import ConservedClaim
from ..derivation import find_witness, lean_point
from ..expr import E, diff, lit, simplify, to_lean, var
from .eulerlagrange import (NONZERO, UNFOLD, _domain_intro, _env_lean, _points, _solve, el_exprs,
                            neval, phys_ok, qeval)

mp.mp.dps = 50


def _add(a: E, b: E) -> E: return simplify(E("add", (a, b)))
def _mul(a: E, b: E) -> E: return simplify(E("mul", (a, b)))
def _sub(a: E, b: E) -> E: return simplify(E("sub", (a, b)))


def _div(a: E, b: E) -> E:
    if b.kind == "lit" and b.q == 1:
        return a
    return simplify(E("div", (a, b)))


def dt_expr(c: ConservedClaim, e: E) -> E:
    """Python mirror of `dt n e`: Σ ∂e/∂q_j q̇_j + ∂e/∂q̇_j q̈_j."""
    out = lit(0)
    for q in c.coords:
        out = _add(out, _mul(diff(e, q), var(f"{q}_dot")))
        out = _add(out, _mul(diff(e, f"{q}_dot"), var(f"{q}_ddot")))
    return out


def hessian(c: ConservedClaim, els: list[E]) -> list[list[E]]:
    return [[diff(els[k], f"{q}_ddot") for q in c.coords] for k in range(c.n)]


def multipliers(c: ConservedClaim, els: list[E]) -> list[E] | None:
    """λ with Σ_k λ_k H_kj = ∂Q/∂q̇_j (H symmetric: λ = H⁻¹ ∂Q/∂q̇)."""
    H = hessian(c, els)
    b = [diff(c.quantity, f"{q}_dot") for q in c.coords]
    if c.n == 1:
        return [_div(b[0], H[0][0])]
    if c.n == 2:
        if all(H[i][j].kind == "lit" and H[i][j].q == 0 for i, j in ((0, 1), (1, 0))):
            return [_div(b[0], H[0][0]), _div(b[1], H[1][1])]
        det = _sub(_mul(H[0][0], H[1][1]), _mul(H[0][1], H[1][0]))
        return [_div(_sub(_mul(b[0], H[1][1]), _mul(b[1], H[1][0])), det),
                _div(_sub(_mul(b[1], H[0][0]), _mul(b[0], H[0][1])), det)]
    return None


def _all_exprs(c: ConservedClaim) -> list[E]:
    return [c.lagrangian, c.quantity]


def in_domain(c: ConservedClaim, env: dict, extra: list[E] = ()) -> bool:
    for op, a, b in c.domain:
        x, y = neval(a, env), neval(b, env)
        if not {">": x > y, "<": x < y, "!=": x != y}[op]:
            return False
    return all(phys_ok(e, env) for e in [*_all_exprs(c), *extra])


def looks_conserved(c: ConservedClaim, els: list[E], lams: list[E], rng: random.Random) -> bool:
    dQ = dt_expr(c, c.quantity)
    n = 0
    for env in _points(c, rng, 40):
        if not in_domain(c, env, lams):
            continue
        for q in c.coords:
            env[f"{q}_ddot"] = Fraction(rng.randint(-9, 9), rng.randint(1, 4))
        lhs = neval(dQ, env)
        rhs = sum(neval(l, env) * neval(e, env) for l, e in zip(lams, els))
        if abs(lhs - rhs) > mp.mpf(10) ** -30 * (1 + abs(lhs)):
            return False
        n += 1
    return n > 0


# ---------------------------------------------------------------- Lean tactic text

PHYSQ = "Expr.physOK, Expr.eval, Fn.eval"
CLOSE = ("(repeat' apply And.intro) <;> first | trivial | assumption | positivity | linarith | "
         "(apply div_pos <;> assumption) | (intro h; linarith)")


def verified_tactic(c: ConservedClaim, lams: list[E]) -> str:
    idx = c.index()
    w = find_witness(c)
    intro, facts = _domain_intro(c)
    hyps = "".join(f", hd{i}" for i in range(len(c.domain))) + facts
    ls = "[" + ", ".join(to_lean(l, idx) for l in lams) + "]"
    diffok = f"simp [{UNFOLD}{facts}] <;> norm_num [{NONZERO}{facts}]"
    phys = f"simp [{PHYSQ}, {NONZERO}{hyps}] <;> {CLOSE}"
    return f"""refine ⟨{ls}, rfl, by decide, ⟨{lean_point(c, w)}, ?_⟩, ?_⟩
· first | trivial | (simp [Expr.eval, Fn.eval] <;> norm_num)
{intro}
refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
· {diffok}
· intro k hk
  interval_cases k <;> {diffok}
· {phys}
· {diffok}
· {phys}
· simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  (repeat' apply And.intro) <;> first | trivial | ({diffok}) | ({phys})
· simp [lamSum, {UNFOLD}{facts}] <;> field_simp <;> ring"""


def _det_simp(n: int) -> str:
    return {1: "Matrix.det_unique", 2: "Matrix.det_fin_two"}[n]


def _trig_hints(es: list[E], env: dict) -> list[str]:
    hints, seen = [], set()

    def walk(e: E):
        if e.kind == "app" and e.name in ("sin", "cos"):
            x = qeval(e.args[0], env)
            if x is not None and x != 0 and abs(x) <= 1 and x not in seen:
                seen.add(x)
                lx = f"(({x.numerator} : ℝ) / {x.denominator})"
                for fn in ("sin", "cos"):
                    hints.append(f"abs_le.mp (Real.{fn}_bound (x := {lx}) (by norm_num [abs_le]))")
        for a in e.args:
            walk(a)

    for e in es:
        walk(e)
    return hints


def refuted_tactic(c: ConservedClaim, env_lean: str, exact: bool, hints: list[str]) -> str:
    n = c.n
    unf = f"{UNFOLD}, dt, timeDir"
    hint = "".join(f"\n  have hb{i} := {h}" for i, h in enumerate(hints))
    names = " ".join(f"hb{i}" for i in range(len(hints)))
    if exact:
        el = f"intro k hk; interval_cases k <;> simp [{unf}] <;> norm_num"
        ne = f"simp [{unf}] <;> norm_num"
    else:
        el = f"intro k hk; interval_cases k <;> simp [{unf}] <;> field_simp <;> ring"
        ne = (f"simp [{unf}] <;> field_simp <;> norm_num at {names} ⊢ <;> "
              f"first | linarith | nlinarith [{', '.join(f'hb{i}.1, hb{i}.2' for i in range(len(hints)))}]"
              if hints else f"simp [{unf}] <;> field_simp <;> norm_num")
    return f"""refine ⟨by decide, by decide, {env_lean}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· simp [Expr.eval] <;> norm_num
· refine ⟨?_, ?_⟩
  · simp [{UNFOLD}] <;> norm_num [{NONZERO}]
  · intro k hk; interval_cases k <;> simp [{UNFOLD}] <;> norm_num [{NONZERO}]
· simp [{PHYSQ}] <;> norm_num
· simp [{UNFOLD}] <;> norm_num [{NONZERO}]
· simp [{PHYSQ}] <;> norm_num
· {el}
· simp [Regular, {_det_simp(n)}, Matrix.of_apply, Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval] <;> norm_num
·{hint}
  {ne}"""


# ---------------------------------------------------------------- search


def _qdet(M: list[list[Fraction]]) -> Fraction:
    return M[0][0] if len(M) == 1 else M[0][0] * M[1][1] - M[0][1] * M[1][0]


def _cramer(H: list[list[E]], F: list[E]) -> list[E] | None:
    """Symbolic solution of H x = -F (n ≤ 2)."""
    if len(H) == 1:
        return [_div(simplify(E("neg", (F[0],))), H[0][0])]
    if len(H) == 2:
        det = _sub(_mul(H[0][0], H[1][1]), _mul(H[0][1], H[1][0]))
        x0 = _sub(_mul(H[0][1], F[1]), _mul(H[1][1], F[0]))
        x1 = _sub(_mul(H[1][0], F[0]), _mul(H[0][0], F[1]))
        return [_div(x0, det), _div(x1, det)]
    return None


def jets(c: ConservedClaim, els: list[E], rng: random.Random):
    """Candidate counterexample jets on the EL surface, with an invertible Hessian and
    dQ/dt != 0: ("exact", w) with every slot rational, or ("symbolic", env, sol) where
    q̈ = sol (an Expr) evaluated at the rational point env."""
    from ..expr import substitute
    acc = [f"{q}_ddot" for q in c.coords]
    H = hessian(c, els)
    dQ = dt_expr(c, c.quantity)
    F = [simplify(substitute(e, {a: lit(0) for a in acc})) for e in els]     # EL at q̈ = 0
    for env in _points(c, rng, 80):
        if not in_domain(c, env):
            continue
        Hq = [[qeval(h, env) for h in row] for row in H]
        Fq = [qeval(f, env) for f in F]
        if all(None not in row for row in Hq) and None not in Fq:
            if _qdet(Hq) == 0:
                continue
            w = dict(env)
            w.update(zip(acc, _solve(Hq, [-f for f in Fq])))
            d = qeval(dQ, w)
            if d is not None and d != 0:
                yield "exact", w
            continue
        # irrational trig values: q̈ := the symbolic solution, evaluated in Lean at the point
        if c.n > 2 or any(abs(env[q]) > 1 for q in c.coords):
            continue
        Hn = [[neval(h, env) for h in row] for row in H]
        if abs(Hn[0][0] if c.n == 1 else Hn[0][0] * Hn[1][1] - Hn[0][1] * Hn[1][0]) < mp.mpf("1e-6"):
            continue
        sol = _cramer(H, F)
        w = dict(env)
        w.update({a: neval(s, env) for a, s in zip(acc, sol)})
        if abs(neval(dQ, w)) > mp.mpf("1e-3"):
            yield "symbolic", env, sol


def refutations(c: ConservedClaim, els: list[E], rng: random.Random) -> list[tuple[str, str]]:
    acc = [f"{q}_ddot" for q in c.coords]
    out = []
    for j in jets(c, els, rng):
        if j[0] == "exact":
            return [("refuted", refuted_tactic(c, _env_lean(c, j[1]), True, []))]
        _, env, sol = j
        base, idx = _env_lean(c, env), c.index()
        over = {a: f"Expr.eval {base} {to_lean(s, idx)}" for a, s in zip(acc, sol)}
        hints = _trig_hints([c.lagrangian, c.quantity], env)
        out.append(("refuted", refuted_tactic(c, _env_lean(c, env, over), False, hints)))
        if len(out) >= 2:
            break
    return out


def propose(c: ConservedClaim, seed: int = 0) -> list[tuple[str, str]]:
    rng = random.Random(seed)
    els = el_exprs(c)
    lams = multipliers(c, els)
    if lams is not None and looks_conserved(c, els, lams, rng):
        return [("verified", verified_tactic(c, lams))]
    return refutations(c, els, rng)
