"""Untrusted proof search for derivation claims (`physverify/derivation.py`).

Mirrors the Lean `EL` in Python, then

* if the claimed equations look equivalent at random points, builds a certificate matrix
  `C = M A⁻¹` (M = ∂EL/∂qddot, A = ∂(lhs − rhs)/∂qddot) and tactics proving
  `EL_k = Σ_j C_kj (lhs_j − rhs_j)` and `det C ≠ 0` on the domain;
* otherwise searches for a counterexample jet: rational q, qdot and parameters, with qddot
  either solving the EL system exactly (rational case) or set to the claimed right-hand side
  (transcendental case, closed with Mathlib's bounds on sin and cos).

Nothing here is trusted: the judge only asks Lean whether the tactics prove its statement.
"""

from __future__ import annotations

import itertools
import random
from fractions import Fraction

import mpmath as mp

from ..derivation import Claim
from ..expr import E, PI, diff, lit, simplify, to_lean, var

mp.mp.dps = 50

# ---------------------------------------------------------------- symbolic EL (Python mirror)


def el_exprs(c: Claim) -> list[E]:
    out = []
    for q in c.coords:
        P = diff(c.lagrangian, f"{q}_dot")
        terms = []
        for qj in c.coords:
            terms.append(E("mul", (diff(P, qj), var(f"{qj}_dot"))))
            terms.append(E("mul", (diff(P, f"{qj}_dot"), var(f"{qj}_ddot"))))
        dt = terms[0]
        for t in terms[1:]:
            dt = E("add", (dt, t))
        out.append(simplify(E("sub", (dt, diff(c.lagrangian, q)))))
    return out


def _mul(a: E, b: E) -> E:
    return simplify(E("mul", (a, b)))


def _div(a: E, b: E) -> E:
    if b.kind == "lit" and b.q == 1:
        return a
    return simplify(E("div", (a, b)))


def _sub(a: E, b: E) -> E:
    return simplify(E("sub", (a, b)))


def cert_matrix(c: Claim, els: list[E]) -> list[list[E]] | None:
    n = c.n
    acc = [f"{q}_ddot" for q in c.coords]
    M = [[diff(els[k], a) for a in acc] for k in range(n)]
    ys = [_sub(l, r) for l, r in c.eom]
    A = [[diff(ys[j], a) for a in acc] for j in range(n)]
    if n == 1:
        return [[_div(M[0][0], A[0][0])]]
    if n == 2:
        det = _sub(_mul(A[0][0], A[1][1]), _mul(A[0][1], A[1][0]))
        inv = [[A[1][1], simplify(E("neg", (A[0][1],)))],
               [simplify(E("neg", (A[1][0],))), A[0][0]]]
        out = []
        for k in range(2):
            row = []
            for j in range(2):
                s = simplify(E("add", (_mul(M[k][0], inv[0][j]), _mul(M[k][1], inv[1][j]))))
                row.append(_div(s, det))
            out.append(row)
        return out
    return None


# ---------------------------------------------------------------- evaluation


def neval(e: E, env: dict) -> mp.mpf:
    k, a = e.kind, e.args
    if k == "var": return mp.mpf(env[e.name].numerator) / env[e.name].denominator \
        if isinstance(env[e.name], Fraction) else env[e.name]
    if k == "lit": return mp.mpf(e.q.numerator) / e.q.denominator
    if k == "pi": return mp.pi
    if k == "neg": return -neval(a[0], env)
    x = neval(a[0], env)
    if k in ("add", "sub", "mul", "div"):
        y = neval(a[1], env)
        return {"add": x + y, "sub": x - y, "mul": x * y}[k] if k != "div" else (x / y if y else mp.mpf(0))
    if k == "powi": return x ** int(e.q) if (x != 0 or e.q >= 0) else mp.mpf(0)
    if k == "sqrt": return mp.sqrt(x) if x >= 0 else mp.mpf(0)
    if k == "rpow": return x ** (mp.mpf(e.q.numerator) / e.q.denominator) if x > 0 else mp.mpf("nan")
    return {"sin": mp.sin, "cos": mp.cos, "exp": mp.exp, "log": mp.log}[e.name](x)


def qeval(e: E, env: dict[str, Fraction]) -> Fraction | None:
    """Exact rational value, or None if a transcendental value is irrational."""
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return Fraction(e.q)
    if k == "pi": return None
    xs = [qeval(x, env) for x in a]
    if any(x is None for x in xs): return None
    x = xs[0]
    if k == "neg": return -x
    if k == "add": return x + xs[1]
    if k == "sub": return x - xs[1]
    if k == "mul": return x * xs[1]
    if k == "div": return None if xs[1] == 0 else x / xs[1]
    if k == "powi": return None if (x == 0 and e.q < 0) else x ** int(e.q)
    if k == "app" and x == 0: return {"sin": Fraction(0), "cos": Fraction(1), "exp": Fraction(1)}.get(e.name)
    if k == "app" and e.name == "log" and x == 1: return Fraction(0)
    return None


def phys_ok(e: E, env: dict) -> bool:
    """Mirror of Lean's `Expr.physOK`: no junk division, negative power, sqrt, log or rpow."""
    if not all(phys_ok(a, env) for a in e.args):
        return False
    if e.kind == "div":
        return neval(e.args[1], env) != 0
    if e.kind in ("powi", "rpow") and e.q < 0 and neval(e.args[0], env) == 0:
        return False
    if e.kind == "sqrt" or e.kind == "app" and e.name == "log" or \
            e.kind == "rpow" and Fraction(e.q).denominator != 1:
        return neval(e.args[0], env) > 0
    return True


def in_domain(c: Claim, env: dict) -> bool:
    for op, a, b in c.domain:
        x, y = neval(a, env), neval(b, env)
        if not {">": x > y, "<": x < y, "!=": x != y}[op]:
            return False
    # points with junk values are no use: Verified and Refuted both require PhysOK
    return all(phys_ok(e, env) for e in [c.lagrangian, *(x for eq in c.eom for x in eq)])


def _points(c: Claim, rng: random.Random, count: int):
    """Small rational jets; the first ones put every coordinate at 0 (trig values exact)."""
    vals = [Fraction(1), Fraction(2), Fraction(1, 2), Fraction(3), Fraction(3, 2), Fraction(5, 2)]
    # coordinates stay in [-1, 1]: Mathlib's sin/cos bounds (`Real.sin_bound`) need |x| ≤ 1
    qvals = [Fraction(0), Fraction(1, 2), Fraction(1, 4), Fraction(3, 4)]
    tries = 0
    while tries < count:
        tries += 1
        env: dict[str, Fraction] = {}
        for s in c.params():
            env[s] = rng.choice(vals) * rng.choice([1, 1, 1, -1])
        for i, q in enumerate(c.coords):
            env[q] = (Fraction(0) if tries <= count // 3 else rng.choice(qvals)) + \
                (Fraction(i, 4) if tries % 2 else 0)
            env[f"{q}_dot"] = rng.choice(vals) * rng.choice([1, -1])
            env[f"{q}_ddot"] = Fraction(0)
        if in_domain(c, env):
            yield env


# ---------------------------------------------------------------- Lean tactic text

UNFOLD = ("EL, dt, timeDir, Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval, "
          "Expr.diffOK, Claims, Law.Holds")
# PhysOK (no junk values): unfold, leaving `0 < arg` and `den ≠ 0` goals
PHYS = ("simp [PhysOK, Expr.physOK, Expr.eval, Fn.eval, List.mem_cons, List.not_mem_nil, "
        "forall_eq_or_imp]")
NONZERO = "mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff, zpow_eq_zero_iff, not_or, ne_eq"
# det ≠ 0 when it is not a plain product: clear denominators, then sum-of-positive-terms
DET_CLOSE = ("first | (norm_num) | (field_simp; nlinarith [Real.sin_sq_add_cos_sq (env 0 - env 1), "
             "Real.cos_sq_le_one (env 0 - env 1), sq_nonneg (Real.sin (env 0 - env 1))])")


def _env_lean(c: Claim, env: dict, override: dict[str, str] | None = None) -> str:
    idx = c.index()
    by_index = sorted(idx, key=idx.get)
    items = []
    for s in by_index:
        if override and s in override:
            items.append(override[s])
        else:
            q = Fraction(env[s])
            items.append(f"({q.numerator} : ℝ)" if q.denominator == 1
                         else f"(({q.numerator} : ℝ) / {q.denominator})")
    return "(fun j : ℕ => [" + ", ".join(items) + "].getD j 0)"


def _domain_intro(c: Claim) -> tuple[str, str]:
    """Intro line, and the domain facts as extra simp lemmas (`x ≠ 0` from `0 < x`)."""
    if not c.domain:
        return "intro env _", ""
    names = [f"hd{i}" for i in range(len(c.domain))]
    pat = f"⟨{', '.join(names)}⟩" if len(names) > 1 else names[0]
    facts = []
    for (op, a, b), h in zip(c.domain, names):
        zero_b, zero_a = b.kind == "lit" and b.q == 0, a.kind == "lit" and a.q == 0
        if op == ">" and zero_b or op == "<" and zero_a:
            facts.append(f"{h}.ne'")
        elif op == "<" and zero_b or op == ">" and zero_a:
            facts.append(f"{h}.ne")
        elif op == "!=":
            facts.append(h)
    haves = "".join(f"\nhave hn{i} := {f}" for i, f in enumerate(facts))
    return (f"intro env {pat}\nsimp only [Expr.eval, Rat.cast_zero] at {' '.join(names)}{haves}",
            "".join(", " + f for f in facts))


def _positive_vars(c: Claim) -> dict[str, str]:
    """Symbols the domain makes positive, with the hypothesis name."""
    out = {}
    for i, (op, a, b) in enumerate(c.domain):
        if op == ">" and a.kind == "var" and b.kind == "lit" and b.q == 0:
            out[a.name] = f"hd{i}"
    return out


def _factors(e: E) -> list[E]:
    if e.kind == "mul":
        return _factors(e.args[0]) + _factors(e.args[1])
    if e.kind == "powi" and e.q > 0:
        return _factors(e.args[0])
    if e.kind == "neg":
        return _factors(e.args[0])
    return [e]


def _denominators(e: E) -> list[E]:
    out = []
    if e.kind == "div":
        out += _factors(e.args[1])
    for a in e.args:
        out += _denominators(a)
    return out


def _trig_atoms(e: E, acc: dict) -> dict:
    if e.kind == "app" and e.name in ("sin", "cos"):
        acc[repr(e.args[0])] = e.args[0]
    for a in e.args:
        _trig_atoms(a, acc)
    return acc


def nontrivial_factors(c: Claim, C) -> list[E]:
    """Denominator factors that are not literals or positive symbols, and are positive at
    every sample point (we only try to prove `0 < F`)."""
    pos = _positive_vars(c)
    seen, out = set(), []
    exprs = [r for _, r in c.eom] + [l for l, _ in c.eom] + [x for row in C for x in row]
    rng = random.Random(1)
    pts = list(_points(c, rng, 30))
    for e in exprs:
        for f in _denominators(e):
            if f.kind == "lit" or (f.kind == "var" and f.name in pos) or repr(f) in seen:
                continue
            seen.add(repr(f))
            if pts and all(neval(f, p) > 0 for p in pts):
                out.append(f)
    return out


def _monomial_quotient(c: Claim, num: E, den: E) -> E | None:
    """If num/den is c·Π v^e over positive symbols (checked numerically), return it."""
    pos = sorted(_positive_vars(c))
    rng = random.Random(2)
    pts = list(_points(c, rng, 12))
    if not pts:
        return None

    def r(p):
        d = neval(den, p)
        return neval(num, p) / d if d else None

    base = pts[0]
    r0 = r(base)
    if r0 is None or r0 == 0:
        return None
    exps = {}
    for v in pos:
        p2 = dict(base)
        p2[v] = base[v] * 2
        r2 = r(p2)
        if r2 is None or r2 / r0 <= 0:
            return None
        e = mp.log(r2 / r0, 2)
        if abs(e - round(e)) > mp.mpf("1e-20") or not 0 <= round(e) <= 6:
            return None
        if round(e):
            exps[v] = int(round(e))
    def mono(p):
        return mp.fprod((mp.mpf(p[v].numerator) / p[v].denominator) ** k for v, k in exps.items())

    k0 = r0 / mono(base)
    coef = Fraction(str(mp.nstr(k0, 40))).limit_denominator(1000)
    for p in pts[1:]:
        rp = r(p)
        if rp is None or abs(rp - mono(p) * mp.mpf(coef.numerator) / coef.denominator) > mp.mpf("1e-25") * (1 + abs(rp)):
            return None
    out = lit(coef)
    for v, k in sorted(exps.items()):
        out = E("mul", (out, E("powi", (var(v),), q=k)))
    return simplify(out)


def _det_expr(C) -> E:
    if len(C) == 1:
        return C[0][0]
    return E("sub", (E("mul", (C[0][0], C[1][1])), E("mul", (C[0][1], C[1][0]))))


def verified_tactic(c: Claim, C: list[list[E]]) -> str:
    idx = c.index()
    n = c.n
    rows = "; ".join(", ".join(f"Expr.eval env {to_lean(x, idx)}" for x in row) for row in C)
    det = {1: "Matrix.det_unique", 2: "Matrix.det_fin_two"}[n]
    sums = {1: "Fin.sum_univ_one", 2: "Fin.sum_univ_two"}[n]
    intro, facts = _domain_intro(c)
    pos = _positive_vars(c)
    # positivity of the non-trivial denominator factors, for field_simp and det ≠ 0
    hyps = []
    Fs = nontrivial_factors(c, C)
    for i, F in enumerate(Fs):
        hints = []
        for x in _trig_atoms(F, {}).values():
            lx = f"(Expr.eval env {to_lean(x, idx)})"
            for fn in ("cos", "sin"):
                hints.append(f"Real.{fn}_sq_le_one {lx}")
                hints += [f"mul_nonneg {h}.le (sub_nonneg.2 (Real.{fn}_sq_le_one {lx}))" for h in pos.values()]
        hint_haves = "".join(f"  have hh{j} := {h}\n" for j, h in enumerate(hints))
        hyps.append(f"have hF{i} : 0 < Expr.eval env {to_lean(F, idx)} := by\n{hint_haves}"
                    f"  simp only [Expr.eval, Fn.eval, zpow_ofNat] at *\n"
                    f"  first | positivity | nlinarith\n"
                    f"simp only [Expr.eval, Fn.eval, zpow_ofNat] at hF{i}\n"
                    f"have hFn{i} := hF{i}.ne'")
    det_alt = ""
    D = _det_expr(C)
    for i, F in enumerate(Fs):
        m = _monomial_quotient(c, D, F)
        if m is not None:
            det_alt = (f"\n     | (rw [show Matrix.det !![{rows}] = Expr.eval env {to_lean(m, idx)} * "
                       f"Expr.eval env {to_lean(F, idx)} by simp [{det}, Expr.eval, Fn.eval, zpow_ofNat] <;> ring]; "
                       f"simp only [Expr.eval, Fn.eval, zpow_ofNat]; "
                       f"exact mul_ne_zero (by simp [{NONZERO}{facts}]) hFn{i})")
            break
    have_block = ("\n" + "\n".join(hyps)) if hyps else ""
    # the domain facts themselves (`0 < env i`), so `0 < x` and `q.den = 1 ∨ 0 < x` close;
    # `x ≠ 0` facts and the denominator factors for the `b ≠ 0` goals of divisions
    hyps_simp = "".join(f", hd{i}" for i in range(len(c.domain))) + facts + \
        "".join(f", hFn{i}" for i in range(len(Fs)))
    # the judge has already proved `dimsOK`, `NoAccel` and `∃ env, D env`
    return f"""{intro}{have_block}
refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
· simp [{UNFOLD}{facts}] <;> norm_num [{NONZERO}{facts}]
· intro k hk
  interval_cases k <;> simp [{UNFOLD}{facts}] <;> norm_num [{NONZERO}{facts}]
· {PHYS[:-1]}, {NONZERO}{hyps_simp}] <;> (repeat' apply And.intro) <;> first | assumption | positivity | linarith | (apply div_pos <;> assumption) | (intro h; linarith)
· refine ELSystem_iff_of_cert rfl !![{rows}] ?_ ?_
  · first
     | (simp [{det}, Expr.eval, Fn.eval, {NONZERO}{facts}] <;> ({DET_CLOSE}) <;> done){det_alt}
  · intro k
    fin_cases k <;> simp [{UNFOLD}, {sums}, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp <;> ring"""


def refuted_tactic_rational(c: Claim, env: dict) -> str:
    return f"""refine ⟨by decide, {_env_lean(c, env)}, ?_, ?_, ?_, ?_⟩
{_POINT_DOMAIN}
· intro h
  have hc := h.1 (by intro k hk; interval_cases k <;> simp [{UNFOLD}] <;> norm_num)
  simp [{UNFOLD}] at hc <;> norm_num at hc"""


# D, DomainOK and PhysOK at a concrete point
_POINT_DOMAIN = f"""· simp [Expr.eval] <;> norm_num
· refine ⟨?_, ?_⟩
  · simp [{UNFOLD}] <;> norm_num [{NONZERO}]
  · intro k hk; interval_cases k <;> simp [{UNFOLD}] <;> norm_num [{NONZERO}]
· {PHYS} <;> norm_num"""


def refuted_tactic_claims(c: Claim, env: dict, k: int, hints: list[str]) -> str:
    """qddot := claimed rhs at the base point, so the claims hold; then EL_k ≠ 0."""
    idx = c.index()
    base = _env_lean(c, env)
    over = {f"{q}_ddot": f"Expr.eval {base} {to_lean(r, idx)}"
            for q, (l, r) in zip(c.coords, c.eom)}
    hint = "\n".join(f"  have hb{i} := {h}" for i, h in enumerate(hints))
    names = " ".join(f"hb{i}" for i in range(len(hints)))
    return f"""refine ⟨by decide, {_env_lean(c, env, over)}, ?_, ?_, ?_, ?_⟩
{_POINT_DOMAIN}
· intro h
  have hk := h.2 (by simp [{UNFOLD}]) {k} (by norm_num)
{hint}
  simp [{UNFOLD}] at hk <;> norm_num [abs_of_pos] at {names} hk ⊢ <;> first | linarith | nlinarith"""


def _trig_hints(c: Claim, env: dict) -> list[str]:
    """Mathlib bounds for sin/cos at the rational arguments that occur."""
    hints = []
    full = dict(env)
    seen = set()

    def walk(e: E):
        if e.kind == "app" and e.name in ("sin", "cos"):
            x = qeval(e.args[0], full)
            if x is not None and x != 0 and abs(x) <= 1 and x not in seen:
                seen.add(x)   # EL has derivatives of both: bound sin and cos at x
                lx = f"(({x.numerator} : ℝ) / {x.denominator})"
                for fn in ("sin", "cos"):
                    hints.append(f"abs_le.mp (Real.{fn}_bound (x := {lx}) (by norm_num [abs_le]))")
        for a in e.args:
            walk(a)

    walk(c.lagrangian)
    for l, r in c.eom:
        walk(l), walk(r)
    return hints


# ---------------------------------------------------------------- search


def _solve(A: list[list[Fraction]], b: list[Fraction]) -> list[Fraction] | None:
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[i][n] / M[i][i] for i in range(n)]


def looks_equivalent(c: Claim, els: list[E], C, rng: random.Random) -> bool:
    if C is None:
        return False
    ys = [_sub(l, r) for l, r in c.eom]
    n = 0
    for env in _points(c, rng, 40):
        env = {k: v for k, v in env.items()}
        for q in c.coords:
            env[f"{q}_ddot"] = Fraction(rng.randint(-9, 9), rng.randint(1, 4))
        for k in range(c.n):
            lhs = neval(els[k], env)
            rhs = sum(neval(C[k][j], env) * neval(ys[j], env) for j in range(c.n))
            if abs(lhs - rhs) > mp.mpf(10) ** -30 * (1 + abs(lhs)):
                return False
        n += 1
    return n > 0


def propose(c: Claim, seed: int = 0) -> list[tuple[str, str]]:
    rng = random.Random(seed)
    els = el_exprs(c)
    C = cert_matrix(c, els)
    if looks_equivalent(c, els, C, rng):
        return [("verified", verified_tactic(c, C))]
    acc = [f"{q}_ddot" for q in c.coords]
    out = []
    for env in _points(c, rng, 60):
        z = dict(env)
        F = [qeval(e, z) for e in els]
        Mq = [[qeval(diff(e, a), z) for a in acc] for e in els]
        if None not in F and all(None not in row for row in Mq):
            sol = _solve(Mq, [-f for f in F])
            if sol is not None:
                w = dict(env)
                w.update({a: s for a, s in zip(acc, sol)})
                ys = [qeval(_sub(l, r), w) for l, r in c.eom]
                if any(y is not None and y != 0 for y in ys) and all(y is not None for y in ys):
                    out.append(("refuted", refuted_tactic_rational(c, w)))
                    break
        # transcendental: claims solved for qddot, put qddot := rhs
        if all(l.kind == "var" and l.name == a for (l, _), a in zip(c.eom, acc)):
            w = dict(env)
            for a, (_, r) in zip(acc, c.eom):
                w[a] = neval(r, env)
            vals = [neval(e, w) for e in els]
            k = max(range(c.n), key=lambda i: abs(vals[i]))
            if abs(vals[k]) > mp.mpf("1e-3"):
                out.append(("refuted", refuted_tactic_claims(c, env, k, _trig_hints(c, env))))
                if len(out) >= 2:
                    break
    return out[:2]
