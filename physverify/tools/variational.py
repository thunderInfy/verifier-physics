"""Untrusted proof search for variational-integrator claims (`physverify/variational.py`).

* `del_equations`, VERIFIED: the certificate matrix `C = M A⁻¹` (M = ∂DEL/∂q2,
  A = ∂(lhs − rhs)/∂q2), if `DEL = C · (lhs − rhs)` holds at random points.
* `discrete_momentum_conserved`, VERIFIED: multipliers μ independent of q2 with
  `Mᵀ μ = ∂J(q1, q2)/∂q2` (the q2-coefficients of `J(q1, q2) − J(q0, q1) = Σ μ_k DEL_k`), if the
  identity then holds at random points. For a symmetry with generator ξ this is μ = −ξ(q1).
* REFUTED (both kinds): rational q0, q1, h and parameters, q2 solving DEL exactly when DEL is
  affine in q2 (or the claimed update, for `del_equations`), and the claim failing there.
* `update_conserves` (explicit maps): routed by the exact rational normal form of
  J(Φ(z)) − J(z); VERIFIED by `simp` + `ring1`/`field_simp`, REFUTED at a rational z ∈ D
  where J changes, replayed by `norm_num`.

Nothing here is trusted: the judge only asks Lean whether the tactics prove its statement.
"""

from __future__ import annotations

import random
from fractions import Fraction

import mpmath as mp

from ..derivation import find_witness, lean_point
from ..expr import E, diff, lit, simplify, substitute, to_lean
from ..variational import Integrator, NotPolynomial, UpdateMap, VClaim, del_exprs, update_defect
from .eulerlagrange import (NONZERO, _denominators, _domain_intro, _env_lean, _solve, neval, phys_ok,
                            qeval)

mp.mp.dps = 50


def _add(a: E, b: E) -> E: return simplify(E("add", (a, b)))
def _mul(a: E, b: E) -> E: return simplify(E("mul", (a, b)))
def _sub(a: E, b: E) -> E: return simplify(E("sub", (a, b)))
def _neg(a: E) -> E: return simplify(E("neg", (a,)))


def _div(a: E, b: E) -> E:
    if b.kind == "lit" and b.q == 1:
        return a
    return simplify(E("div", (a, b)))


def q2_jacobian(I: Integrator, es: list[E]) -> list[list[E]]:
    return [[diff(e, I.level(q, 2)) for q in I.coords] for e in es]


def _solve_sym(M: list[list[E]], b: list[E]) -> list[E] | None:
    """Symbolic solution of M x = b (n ≤ 2, Cramer)."""
    if len(M) == 1:
        return [_div(b[0], M[0][0])]
    if len(M) == 2:
        det = _sub(_mul(M[0][0], M[1][1]), _mul(M[0][1], M[1][0]))
        return [_div(_sub(_mul(b[0], M[1][1]), _mul(M[0][1], b[1])), det),
                _div(_sub(_mul(M[0][0], b[1]), _mul(b[0], M[1][0])), det)]
    return None


def cert_matrix(I: Integrator, c: VClaim, dels: list[E]) -> list[list[E]] | None:
    """C = M A⁻¹, i.e. row k of C solves Aᵀ x = M_k."""
    M = q2_jacobian(I, dels)
    A = q2_jacobian(I, [_sub(l, r) for l, r in c.update])
    At = [list(r) for r in zip(*A)]
    rows = [_solve_sym(At, M[k]) for k in range(I.n)]
    return None if None in rows else rows


def multipliers(I: Integrator, c: VClaim, dels: list[E]) -> list[E] | None:
    """μ independent of q2 (the Noether case: μ = −ξ(q1))."""
    M = q2_jacobian(I, dels)
    Mt = [list(r) for r in zip(*M)]
    Jsh = substitute(c.quantity, I.shift())
    return _solve_sym(Mt, [diff(Jsh, I.level(q, 2)) for q in I.coords])


def _at_q2_zero(I: Integrator, e: E) -> E:
    return simplify(substitute(e, {I.level(q, 2): lit(0) for q in I.coords}))


def _poly_expr(a: dict) -> E:
    out = None
    for m, c in sorted(a.items()):
        t = lit(c)
        for v, e in m:
            t = _mul(t, E("powi", (E("var", name=v),), q=e))
        out = t if out is None else _add(out, t)
    return out if out is not None else lit(0)


def _clean(b: E) -> E:
    """b as (c·monomial) · B with B a polynomial with coprime integer coefficients, so that
    the denominator Lean sees is B (`4 m + h² k` rather than `−m/h − h k/4`)."""
    import math

    from ..variational import NotPolynomial, to_poly
    try:
        p = to_poly(b, {})
    except NotPolynomial:
        return b
    if len(p) < 2:
        return b
    names = {v for m in p for v, _ in m}
    low = {v: min(dict(m).get(v, 0) for m in p) for v in names}
    L = math.lcm(*(c.denominator for c in p.values()))
    G = math.gcd(*(c.numerator for c in p.values()))
    c0 = Fraction(G, L) * (-1 if all(c < 0 for c in p.values()) else 1)
    B = {tuple((v, e - low[v]) for v, e in m if e - low[v]): c / c0 for m, c in p.items()}
    mono = {tuple((v, e) for v, e in low.items() if e): c0}
    return _mul(_poly_expr(mono), _poly_expr(B))


def division_multiplier(I: Integrator, c: VClaim, dels: list[E], rng: random.Random,
                        max_deg: int = 4) -> list[E] | None:
    """n = 1, DEL = a + b·q2 affine in q2: μ = (J(q1, q2) − J(q0, q1)) / DEL by synthetic
    division in q2 (for invariants that are not Noether momenta, e.g. quadratic invariants of
    a linear step). The remainder must vanish at random points."""
    if I.n != 1:
        return None
    x2 = I.level(I.coords[0], 2)
    N = _sub(substitute(c.quantity, I.shift()), c.quantity)
    b = _clean(diff(dels[0], x2))
    a = _at_q2_zero(I, dels[0])
    coeffs, d, fact = [], N, 1                      # Taylor coefficients of N in q2
    for i in range(max_deg + 2):
        coeffs.append(_div(_at_q2_zero(I, d), lit(fact)))
        d, fact = diff(d, x2), fact * (i + 1)
    deg = max((i for i, e in enumerate(coeffs) if not (e.kind == "lit" and e.q == 0)), default=0)
    if deg == 0 or deg > max_deg:
        return None
    q = [lit(0)] * deg                               # N = (a + b q2)·Σ q_i q2^i
    q[deg - 1] = _div(coeffs[deg], b)
    for i in range(deg - 1, 0, -1):
        q[i - 1] = _div(_sub(coeffs[i], _mul(a, q[i])), b)
    mu = q[0]
    for i in range(1, deg):
        mu = _add(mu, _mul(q[i], E("powi", (E("var", name=x2),), q=i)))
    return [mu]


# ---------------------------------------------------------------- sampling

_VALS = [Fraction(v) for v in ("1", "2", "1/2", "3", "3/2", "-1", "-1/2", "1/3", "-2", "5/2")]
_HS = [Fraction(v) for v in ("1/2", "1", "1/4", "1/3", "2")]


def _exprs(I: Integrator, c: VClaim) -> list[E]:
    sh = I.shift()
    out = [I.ld, substitute(I.ld, sh)]
    if c.kind == "discrete_momentum_conserved":
        out += [c.quantity, substitute(c.quantity, sh)]
    if c.kind == "del_equations":
        out += [x for eq in c.update for x in eq]
    return out


def in_domain(I: Integrator, c: VClaim, env: dict, extra=()) -> bool:
    for op, a, b in I.domain:
        x, y = neval(a, env), neval(b, env)
        if not {">": x > y, "<": x < y, "!=": x != y}[op]:
            return False
    return all(phys_ok(e, env) for e in [*_exprs(I, c), *extra])


def points(I: Integrator, rng: random.Random, count: int, q2: bool = True):
    for _ in range(count):
        env = {s: rng.choice(_VALS) for s in I.params()}
        env["h"] = rng.choice(_HS)
        for q in I.coords:
            for j in range(3 if q2 else 2):
                env[I.level(q, j)] = rng.choice(_VALS)
            if not q2:
                env[I.level(q, 2)] = Fraction(0)
        yield env


def _close(x, y) -> bool:
    return abs(x - y) <= mp.mpf(10) ** -30 * (1 + abs(x))


def looks_equivalent(I, c, dels, C, rng) -> bool:
    ys = [_sub(l, r) for l, r in c.update]
    n = 0
    for env in points(I, rng, 40):
        if not in_domain(I, c, env):
            continue
        for k in range(I.n):
            if not _close(neval(dels[k], env), sum(neval(C[k][j], env) * neval(ys[j], env) for j in range(I.n))):
                return False
        n += 1
    return n > 0


def looks_conserved(I, c, dels, mus, rng) -> bool:
    Jsh = substitute(c.quantity, I.shift())
    n = 0
    for env in points(I, rng, 40):
        if not in_domain(I, c, env, mus):
            continue
        lhs = neval(Jsh, env) - neval(c.quantity, env)
        if not _close(lhs, sum(neval(m, env) * neval(d, env) for m, d in zip(mus, dels))):
            return False
        n += 1
    return n > 0


def solve_q2(I: Integrator, es: list[E], env: dict) -> dict | None:
    """q2 with es(q0, q1, q2) = 0 exactly, when es is affine in q2 at this (q0, q1)."""
    z = dict(env)
    for q in I.coords:
        z[I.level(q, 2)] = Fraction(0)
    F = [qeval(e, z) for e in es]
    M = [[qeval(x, z) for x in row] for row in q2_jacobian(I, es)]
    if None in F or any(None in r for r in M):
        return None
    sol = _solve(M, [-f for f in F])
    if sol is None:
        return None
    w = dict(env)
    w.update({I.level(q, 2): s for q, s in zip(I.coords, sol)})
    if any(qeval(e, w) != 0 for e in es):        # not affine in q2: no exact rational step
        return None
    return w


def _det(M: list[list[Fraction]]) -> Fraction:
    return M[0][0] if len(M) == 1 else M[0][0] * M[1][1] - M[0][1] * M[1][0]


def regular(I: Integrator, dels: list[E], w: dict) -> bool:
    M = [[qeval(x, w) for x in row] for row in q2_jacobian(I, dels)]
    return all(None not in r for r in M) and _det(M) != 0


# ---------------------------------------------------------------- Lean tactic text

UNF = "DEL, Expr.deriv, Expr.dir, Expr.basis, Expr.ren, shift, Expr.eval, Fn.eval, Expr.diffOK"
PHYSU = "Expr.physOK, Expr.ren, shift, Expr.eval, Fn.eval, Real.sqrt_ne_zero', Real.sqrt_pos"
CLOSE = ("(repeat' apply And.intro) <;> first | trivial | assumption | positivity | linarith | "
         "(apply div_pos <;> assumption) | (intro h; linarith)")
# `ring` falls back to `ring_nf` without failing, so `first` would stop there: use `ring1`
IDENT = "first | rfl | ring1 | (field_simp; done) | (field_simp; ring1)"


def _intro(I: Integrator):
    intro, facts = _domain_intro(I)
    hyps = "".join(f", hd{i}" for i in range(len(I.domain))) + facts
    return intro, facts, hyps


def _sign_close(I: Integrator) -> str:
    """Closer for `0 < e` / `e ≠ 0` goals with e a rational function of the positive symbols
    (`4 m + h² k ≠ 0`): clear denominators, then nlinarith with products of the domain facts."""
    pos = [f"hd{i}" for i, (op, a, b) in enumerate(I.domain)
           if op == ">" and a.kind == "var" and b.kind == "lit" and b.q == 0]
    hints = pos + [f"mul_pos {x} {y}" for i, x in enumerate(pos) for y in pos[i:]]
    hs = ", ".join(hints)
    return f"(intro hz; field_simp at hz; nlinarith [{hs}]) | (field_simp; nlinarith [{hs}])"


def del_verified_tactic(I: Integrator, C: list[list[E]]) -> str:
    idx, n = I.index(), I.n
    intro, facts, hyps = _intro(I)
    rows = "; ".join(", ".join(f"Expr.eval env {to_lean(x, idx)}" for x in row) for row in C)
    det = {1: "Matrix.det_unique", 2: "Matrix.det_fin_two"}[n]
    sums = {1: "Fin.sum_univ_one", 2: "Fin.sum_univ_two"}[n]
    diffok = f"simp [{UNF}{facts}] <;> norm_num [{NONZERO}, Real.sqrt_ne_zero'{hyps}]"
    phys = f"simp [PhysOK, {PHYSU}, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, {NONZERO}{hyps}] <;> {CLOSE} | {_sign_close(I)}"
    return f"""{intro}
refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
· {diffok}
· {diffok}
· {phys}
· {phys}
· refine DELSystem_iff_of_cert rfl !![{rows}] ?_ ?_
  · simp [{det}, Expr.eval, Fn.eval, {NONZERO}{facts}] <;> (repeat' apply And.intro) <;> first | (norm_num; done) | assumption | {_sign_close(I)}
  · intro k
    fin_cases k <;> simp [{UNF}, {sums}, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] <;> {IDENT}"""


def _point_steps(I: Integrator) -> str:
    """D, StepOK and the physOK conjuncts of L_d at a concrete point."""
    return f"""· simp [Expr.eval] <;> norm_num
· refine ⟨?_, ?_⟩ <;> simp [{UNF}] <;> norm_num [{NONZERO}]"""


def del_refuted_tactic(I: Integrator, w: dict, del_holds: bool) -> str:
    env = _env_lean(I, w)
    # DEL holds and the update fails, or the update holds and DEL fails
    if del_holds:
        close = f"""  have hc := h.1 (by intro k hk; interval_cases k <;> simp [{UNF}] <;> norm_num)
  simp [Claims, Law.Holds, Expr.eval] at hc <;> norm_num at hc"""
    else:
        close = f"""  have hc := h.2 (by simp [Claims, Law.Holds, Expr.eval] <;> norm_num)
  have := hc 0 (by norm_num)
  simp [{UNF}] at this <;> norm_num at this"""
    return f"""refine ⟨by decide, {env}, ?_, ?_, ?_, ?_, ?_⟩
{_point_steps(I)}
· simp [PhysOK, {PHYSU}, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] <;> norm_num
· simp [{PHYSU}] <;> norm_num
· intro h
{close}"""


def mom_verified_tactic(I: Integrator, mus: list[E]) -> str:
    idx = I.index()
    w = find_witness(I)
    intro, facts, hyps = _intro(I)
    ms = "[" + ", ".join(to_lean(m, idx) for m in mus) + "]"
    diffok = f"simp [{UNF}{facts}] <;> norm_num [{NONZERO}, Real.sqrt_ne_zero'{hyps}]"
    phys = f"simp [{PHYSU}, {NONZERO}{hyps}] <;> {CLOSE} | {_sign_close(I)}"
    # the multipliers' denominators are non-zero on D: stated first, so field_simp can use them
    dens, seen = [], set()
    for m in mus:
        for d in _denominators(m):
            if repr(d) not in seen and not (d.kind == "lit" or d.kind == "var"):
                seen.add(repr(d))
                dens.append(d)
    haves = "".join(
        f"\nhave hden{i} : Expr.eval env {to_lean(d, idx)} ≠ 0 := by\n"
        f"  simp [Expr.eval, Fn.eval, {NONZERO}{hyps}] <;> {CLOSE} | {_sign_close(I)}\n"
        f"simp [Expr.eval, Fn.eval] at hden{i}" for i, d in enumerate(dens))
    return f"""refine ⟨{ms}, rfl, ⟨{lean_point(I, w)}, ?_⟩, ?_⟩
· first | trivial | (simp [Expr.eval, Fn.eval] <;> norm_num)
{intro}{haves}
refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
· {diffok}
· {diffok}
· {phys}
· {phys}
· {phys}
· {phys}
· simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  (repeat' apply And.intro) <;> first | trivial | ({phys})
· simp [delSum, {UNF}{facts}] <;> {IDENT}"""


def mom_refuted_tactic(I: Integrator, w: dict) -> str:
    det = {1: "Matrix.det_unique", 2: "Matrix.det_fin_two"}[I.n]
    return f"""refine ⟨by decide, by decide, {_env_lean(I, w)}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
{_point_steps(I)}
· simp [{PHYSU}] <;> norm_num
· simp [{PHYSU}] <;> norm_num
· simp [{PHYSU}] <;> norm_num
· simp [{PHYSU}] <;> norm_num
· intro k hk; interval_cases k <;> simp [{UNF}] <;> norm_num
· refine ⟨fun i hi => ?_, ?_⟩
  · interval_cases i <;> simp [{UNF}] <;> norm_num [{NONZERO}]
  · simp [RegularStep, {det}, Matrix.of_apply, {UNF}] <;> norm_num
· simp [{PHYSU}] <;> norm_num"""


# ---------------------------------------------------------------- search

def refute_del(I: Integrator, c: VClaim, dels: list[E], rng: random.Random):
    ys = [_sub(l, r) for l, r in c.update]
    for env in points(I, rng, 60, q2=False):
        for es, other, holds in ((dels, ys, True), (ys, dels, False)):
            w = solve_q2(I, es, env)
            if w is None or not in_domain(I, c, w):
                continue
            vals = [qeval(e, w) for e in other]
            if None not in vals and any(vals):
                return ("refuted", del_refuted_tactic(I, w, holds))
    return None


def refute_momentum(I: Integrator, c: VClaim, dels: list[E], rng: random.Random):
    Jsh = substitute(c.quantity, I.shift())
    for env in points(I, rng, 60, q2=False):
        w = solve_q2(I, dels, env)
        if w is None or not in_domain(I, c, w) or not regular(I, dels, w):
            continue
        a, b = qeval(Jsh, w), qeval(c.quantity, w)
        if a is not None and b is not None and a != b:
            return ("refuted", mom_refuted_tactic(I, w))
    return None


def refutation_point(I: Integrator, c: VClaim, seed: int = 0) -> dict | None:
    """The rational point a momentum refutation uses (for tests and reports)."""
    rng = random.Random(seed)
    dels = del_exprs(I)
    Jsh = substitute(c.quantity, I.shift())
    for env in points(I, rng, 60, q2=False):
        w = solve_q2(I, dels, env)
        if w is not None and in_domain(I, c, w) and regular(I, dels, w) and \
                qeval(Jsh, w) != qeval(c.quantity, w):
            return w
    return None


# ---------------------------------------------------------------- explicit update maps

UPD = "updateStep, updAux, Function.update_apply"
PHYS1 = "Expr.physOK, Expr.eval, Fn.eval, Real.sqrt_ne_zero', Real.sqrt_pos"


def update_points(U: UpdateMap, rng: random.Random, count: int):
    for _ in range(count):
        env = {s: rng.choice(_VALS) for s in U.params()}
        env["h"] = rng.choice(_HS)
        env.update({z: rng.choice(_VALS) for z in U.state})
        yield env


def update_point_ok(U: UpdateMap, c: VClaim, env: dict) -> dict | None:
    """The state after the step if `env` is in D and Φ, J (at z and Φ(z)) are junk-free there."""
    for op, a, b in U.domain:
        x, y = qeval(a, env), qeval(b, env)
        if x is None or y is None or not {">": x > y, "<": x < y, "!=": x != y}[op]:
            return None
    if not all(phys_ok(e, env) for e in [*U.phi, c.quantity]):
        return None
    new = [qeval(e, env) for e in U.phi]
    if None in new:
        return None
    after = {**env, **dict(zip(U.state, new))}
    return after if phys_ok(c.quantity, after) else None


def update_refutation_point(U: UpdateMap, c: VClaim, seed: int = 0) -> dict | None:
    """A rational z ∈ D (h > 0) with J(Φ(z)) ≠ J(z), exactly."""
    rng = random.Random(seed)
    for env in update_points(U, rng, 200):
        after = update_point_ok(U, c, env)
        if after is None:
            continue
        a, b = qeval(c.quantity, after), qeval(c.quantity, env)
        if a is not None and b is not None and a != b:
            return env
    return None


def update_verified_tactic(U: UpdateMap, c: VClaim) -> str:
    idx = U.index()
    intro, facts, hyps = _intro(U)
    phys = f"simp [{PHYS1}, {NONZERO}{hyps}] <;> {CLOSE} | {_sign_close(U)}"
    dens, seen = [], set()
    for e in [*U.phi, c.quantity]:
        for d in _denominators(e):
            if repr(d) not in seen and not (d.kind == "lit" or d.kind == "var"):
                seen.add(repr(d))
                dens.append(d)
    haves = "".join(
        f"\nhave hden{i} : Expr.eval env {to_lean(d, idx)} ≠ 0 := by\n"
        f"  simp [Expr.eval, Fn.eval, {NONZERO}{hyps}] <;> {CLOSE} | {_sign_close(U)}\n"
        f"simp [Expr.eval, Fn.eval] at hden{i}" for i, d in enumerate(dens))
    dh = "".join(f", hden{i}" for i in range(len(dens)))
    return f"""{intro}{haves}
refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
· simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  (repeat' apply And.intro) <;> first | trivial | ({phys})
· {phys}
· simp [{UPD}, {PHYS1}, {NONZERO}{hyps}{dh}] <;> {CLOSE} | {_sign_close(U)}
· simp [{UPD}, Expr.eval, Fn.eval{facts}] <;> {IDENT}"""


def update_refuted_tactic(U: UpdateMap, w: dict) -> str:
    return f"""refine ⟨{_env_lean(U, w)}, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
· simp [Expr.eval] <;> norm_num
· simp [List.mem_cons, List.not_mem_nil, forall_eq_or_imp, {PHYS1}] <;> norm_num
· simp [{PHYS1}] <;> norm_num
· simp [{UPD}, {PHYS1}] <;> norm_num
· simp [{UPD}, Expr.eval, Fn.eval] <;> norm_num"""


def propose_update(U: UpdateMap, c: VClaim, seed: int = 0) -> list[tuple[str, str]]:
    """Route by the exact normal form of J(Φ(z)) − J(z) when it exists (numerator ≡ 0:
    verified; else a rational point where it is nonzero: refuted). Outside the rational
    fragment, try both. Nothing here is trusted."""
    if c.kind != "update_conserves":
        return []
    try:
        num, _ = update_defect(U, c)
        zero = not num
    except NotPolynomial:
        zero = None
    out = []
    if zero is not False and find_witness(U) is not None:
        out.append(("verified", update_verified_tactic(U, c)))
    if zero is not True:
        w = update_refutation_point(U, c, seed)
        if w is not None:
            out.append(("refuted", update_refuted_tactic(U, w)))
    return out


def propose(I: Integrator, c: VClaim, seed: int = 0) -> list[tuple[str, str]]:
    if isinstance(I, UpdateMap):
        return propose_update(I, c, seed)
    rng = random.Random(seed)
    dels = del_exprs(I)
    if c.kind == "del_equations":
        C = cert_matrix(I, c, dels)
        if C is not None and looks_equivalent(I, c, dels, C, rng):
            return [("verified", del_verified_tactic(I, C))]
        r = refute_del(I, c, dels, rng)
        return [r] if r else []
    if c.kind == "discrete_momentum_conserved":
        for mus in (multipliers(I, c, dels), division_multiplier(I, c, dels, rng)):
            if mus is not None and looks_conserved(I, c, dels, mus, rng):
                return [("verified", mom_verified_tactic(I, mus))]
        r = refute_momentum(I, c, dels, rng)
        return [r] if r else []
    return []
