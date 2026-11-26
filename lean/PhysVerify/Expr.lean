import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Expressions, dimensions, and unit covariance

The trusted core of the verifier. A theory's laws are `Expr` trees (serialized
node-for-node from Python). We define

* `Expr.eval`   — real-valued semantics,
* `Expr.dimOf`  — a computable dimension checker over the 7 SI base dimensions,
* `rescale`     — re-expressing every quantity in different units.

Main results:

* `Expr.eval_rescale` (covariance): a well-dimensioned expression of dimension `d`
  scales by exactly `scale s d` under a change of units `s`.
* `Law.dimMismatch_degenerate`: if the two sides of a law have different dimensions,
  then *if the law is unit-covariant* it can only ever hold where both sides vanish.
* `Law.dimMismatch_refutes`: hence, given any state where the law holds non-trivially,
  the law is not unit-covariant — i.e. it is not a law of nature under assumption
  `unit-covariance` ("physics does not depend on the choice of units").
-/

namespace PhysVerify

/-- Exponents of the 7 SI base dimensions, in order L M T I Θ N J. -/
abbrev Dim := Fin 7 → ℤ

inductive Fn | sin | cos | exp | log
  deriving DecidableEq, Repr

inductive Expr
  | var (i : ℕ)
  | lit (q : ℚ)
  | pi
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | powi (a : Expr) (n : ℤ)
  /-- requires all dimension exponents of `a` to be even -/
  | sqrt (a : Expr)
  /-- real power with rational exponent; `a` must be dimensionless -/
  | rpow (a : Expr) (q : ℚ)
  /-- transcendental function; argument must be dimensionless -/
  | app (f : Fn) (a : Expr)
  deriving Repr

noncomputable def Fn.eval : Fn → ℝ → ℝ
  | .sin => Real.sin
  | .cos => Real.cos
  | .exp => Real.exp
  | .log => Real.log

noncomputable def Expr.eval (env : ℕ → ℝ) : Expr → ℝ
  | .var i => env i
  | .lit q => q
  | .pi => Real.pi
  | .neg a => -a.eval env
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => a.eval env / b.eval env
  | .powi a n => a.eval env ^ n
  | .sqrt a => Real.sqrt (a.eval env)
  | .rpow a q => a.eval env ^ (q : ℝ)
  | .app f a => f.eval (a.eval env)

/-- `some (d/2)` if every exponent of `d` is even. -/
def halfDim (d : Dim) : Option Dim :=
  if ∀ i, d i % 2 = 0 then some (fun i => d i / 2) else none

def Expr.dimOf (ctx : List Dim) : Expr → Option Dim
  | .var i => ctx[i]?
  | .lit _ => some 0
  | .pi => some 0
  | .neg a => a.dimOf ctx
  | .add a b | .sub a b =>
      match a.dimOf ctx, b.dimOf ctx with
      | some x, some y => if x = y then some x else none
      | _, _ => none
  | .mul a b =>
      match a.dimOf ctx, b.dimOf ctx with
      | some x, some y => some (x + y)
      | _, _ => none
  | .div a b =>
      match a.dimOf ctx, b.dimOf ctx with
      | some x, some y => some (x - y)
      | _, _ => none
  | .powi a n => (a.dimOf ctx).map (n • ·)
  | .sqrt a => (a.dimOf ctx).bind halfDim
  | .rpow a _ | .app _ a =>
      match a.dimOf ctx with
      | some x => if x = 0 then some 0 else none
      | none => none

/-! ### Changes of units -/

/-- Numerical factor by which a quantity of dimension `d` changes when each base
unit is rescaled by `s i`. -/
noncomputable def scale (s : Fin 7 → ℝ) (d : Dim) : ℝ := ∏ i, s i ^ d i

/-- Re-express every variable in new units (variable `i` has dimension `ctx[i]`). -/
noncomputable def rescale (s : Fin 7 → ℝ) (ctx : List Dim) (env : ℕ → ℝ) : ℕ → ℝ :=
  fun i => scale s (ctx.getD i 0) * env i

section scale
variable {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i)
include hs

omit hs in
@[simp] lemma scale_zero : scale s 0 = 1 := by simp [scale]

lemma scale_pos (d : Dim) : 0 < scale s d :=
  Finset.prod_pos fun i _ => zpow_pos (hs i) _

lemma scale_add (x y : Dim) : scale s (x + y) = scale s x * scale s y := by
  simp only [scale, Pi.add_apply, zpow_add₀ (hs _).ne', Finset.prod_mul_distrib]

lemma scale_sub (x y : Dim) : scale s (x - y) = scale s x / scale s y := by
  simp only [scale, Pi.sub_apply, zpow_sub₀ (hs _).ne', Finset.prod_div_distrib]

omit hs in
lemma scale_zsmul (n : ℤ) (x : Dim) : scale s (n • x) = scale s x ^ n := by
  simp only [scale, Pi.smul_apply, smul_eq_mul, mul_comm n, zpow_mul, Finset.prod_zpow]

end scale

lemma halfDim_spec {d h : Dim} (hd : halfDim d = some h) : d = h + h := by
  unfold halfDim at hd
  split_ifs at hd with he
  cases hd
  funext i
  have := he i
  simp only [Pi.add_apply]
  omega

/-- **Covariance.** A well-dimensioned expression of dimension `d` transforms by
exactly `scale s d` under a change of units. -/
theorem Expr.eval_rescale {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (ctx : List Dim)
    (env : ℕ → ℝ) : ∀ (e : Expr) (d : Dim), e.dimOf ctx = some d →
      e.eval (rescale s ctx env) = scale s d * e.eval env
  | .var i, d, h => by
      simp only [dimOf] at h
      simp [eval, rescale, List.getD_eq_getElem?_getD, h]
  | .lit q, d, h => by
      simp only [dimOf, Option.some.injEq] at h; subst h; simp [eval]
  | .pi, d, h => by
      simp only [dimOf, Option.some.injEq] at h; subst h; simp [eval]
  | .neg a, d, h => by
      simp only [dimOf] at h
      simp [eval, eval_rescale hs ctx env a d h]
  | .add a b, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> cases hb : b.dimOf ctx <;> simp only [ha, hb] at h <;>
        try contradiction
      rename_i x y
      split_ifs at h with hxy
      cases h; subst hxy
      simp [eval, eval_rescale hs ctx env a _ ha, eval_rescale hs ctx env b _ hb, mul_add]
  | .sub a b, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> cases hb : b.dimOf ctx <;> simp only [ha, hb] at h <;>
        try contradiction
      rename_i x y
      split_ifs at h with hxy
      cases h; subst hxy
      simp [eval, eval_rescale hs ctx env a _ ha, eval_rescale hs ctx env b _ hb, mul_sub]
  | .mul a b, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> cases hb : b.dimOf ctx <;> simp only [ha, hb] at h <;>
        try contradiction
      cases h
      simp only [eval, eval_rescale hs ctx env a _ ha, eval_rescale hs ctx env b _ hb,
        scale_add hs]
      ring
  | .div a b, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> cases hb : b.dimOf ctx <;> simp only [ha, hb] at h <;>
        try contradiction
      cases h
      simp only [eval, eval_rescale hs ctx env a _ ha, eval_rescale hs ctx env b _ hb,
        scale_sub hs]
      rw [mul_div_mul_comm]
  | .powi a n, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> simp only [ha, Option.map_none, Option.map_some,
        Option.some.injEq, reduceCtorEq] at h
      subst h
      simp only [eval, eval_rescale hs ctx env a _ ha, scale_zsmul, mul_zpow]
  | .sqrt a, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> simp only [ha, Option.bind_none, Option.bind_some,
        reduceCtorEq] at h
      rename_i x
      have hx := halfDim_spec h
      simp only [eval, eval_rescale hs ctx env a _ ha, hx, scale_add hs,
        Real.sqrt_mul (mul_nonneg (scale_pos hs d).le (scale_pos hs d).le),
        Real.sqrt_mul_self (scale_pos hs d).le]
  | .rpow a q, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> simp only [ha, reduceCtorEq] at h
      rename_i x
      split_ifs at h with hx
      cases h; subst hx
      simp [eval, eval_rescale hs ctx env a _ ha]
  | .app f a, d, h => by
      simp only [dimOf] at h
      cases ha : a.dimOf ctx <;> simp only [ha, reduceCtorEq] at h
      rename_i x
      split_ifs at h with hx
      cases h; subst hx
      simp [eval, eval_rescale hs ctx env a _ ha]

/-! ### Laws and the dimensional-mismatch refutation -/

structure Law where
  lhs : Expr
  rhs : Expr

def Law.Holds (l : Law) (env : ℕ → ℝ) : Prop := l.lhs.eval env = l.rhs.eval env

/-- A law is unit-covariant if, whenever it holds in some state, it still holds when
that same state is expressed in any other system of units. -/
def Law.UnitCovariant (ctx : List Dim) (l : Law) : Prop :=
  ∀ (env : ℕ → ℝ) (s : Fin 7 → ℝ), (∀ i, 0 < s i) → l.Holds env → l.Holds (rescale s ctx env)

/-- The computable check the judge runs inside the kernel (`by decide`). -/
def Law.dimMismatch (ctx : List Dim) (l : Law) : Bool :=
  match l.lhs.dimOf ctx, l.rhs.dimOf ctx with
  | some x, some y => decide (x ≠ y)
  | _, _ => false

/-- Rescale only base dimension `k`, by a factor of 2. -/
noncomputable def probe (k : Fin 7) : Fin 7 → ℝ := fun i => if i = k then 2 else 1

lemma probe_pos (k : Fin 7) : ∀ i, 0 < probe k i := by
  intro i; unfold probe; split_ifs <;> norm_num

lemma scale_probe (k : Fin 7) (d : Dim) : scale (probe k) d = 2 ^ d k := by
  unfold scale
  rw [Finset.prod_eq_single k (fun j _ hj => by simp [probe, hj]) (by simp)]
  simp [probe]

theorem Law.dimMismatch_degenerate {ctx : List Dim} {l : Law}
    (h : l.dimMismatch ctx = true) (hc : l.UnitCovariant ctx) (env : ℕ → ℝ)
    (hl : l.Holds env) : l.lhs.eval env = 0 := by
  unfold dimMismatch at h
  cases ha : l.lhs.dimOf ctx <;> cases hb : l.rhs.dimOf ctx <;> simp only [ha, hb] at h <;>
    try contradiction
  rename_i x y
  have hxy : x ≠ y := by simpa using h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  by_contra hv
  have h2 := hc env (probe k) (probe_pos k) hl
  unfold Holds at h2 hl
  rw [l.lhs.eval_rescale (probe_pos k) ctx env x ha,
    l.rhs.eval_rescale (probe_pos k) ctx env y hb, ← hl, scale_probe, scale_probe] at h2
  have : (2 : ℝ) ^ x k = 2 ^ y k := mul_right_cancel₀ (hl ▸ hv) h2
  exact hk (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) this)

/-- **Refutation by dimensional analysis.** If the sides of a law have different
dimensions and the law holds non-trivially in some state, it is not unit-covariant. -/
theorem Law.dimMismatch_refutes {ctx : List Dim} {l : Law}
    (h : l.dimMismatch ctx = true) (env : ℕ → ℝ) (hl : l.Holds env)
    (hnz : l.lhs.eval env ≠ 0) : ¬ l.UnitCovariant ctx :=
  fun hc => hnz (dimMismatch_degenerate h hc env hl)

end PhysVerify
