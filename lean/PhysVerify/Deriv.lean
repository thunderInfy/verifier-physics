import PhysVerify.Expr
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Symbolic differentiation of `Expr`, proven correct

`Expr.dir v e` differentiates `e` along a direction in which variable `j` moves with
velocity `v j` (itself an `Expr`). Two special cases are used by the verifier:

* `Expr.deriv i e = e.dir (basis i)`: the partial derivative `∂e/∂x_i`;
* `dt n e` (in `EulerLagrange.lean`): the total time derivative along a trajectory.

`Expr.diffOK env e` is the side condition under which the rules are valid: every
denominator, `log` argument and `sqrt` argument is non-zero, and every negative power
(`powi` with `n < 0`, `rpow` with `q < 1`) has a non-zero base. It is a `Prop` built
structurally from `e`, so it always appears as an explicit hypothesis.

Main results:

* `Expr.hasDerivAt_dir` (chain rule): along any curve `γ` whose coordinates have the
  velocities `v`, `s ↦ e.eval (γ s)` has derivative `(e.dir v).eval (γ t)`.
* `Expr.hasDerivAt_deriv`: `x ↦ e.eval (update env i x)` has derivative
  `(e.deriv i).eval env` at `env i`.
* `Expr.continuousAt_eval` / `Expr.diffOK_eventually`: `diffOK` is an open condition along
  continuous curves.

The output is not simplified. Any simplification happens in untrusted proof search.
-/

namespace PhysVerify
namespace Expr

/-- The variables an expression mentions (with repetitions). -/
def vars : Expr → List ℕ
  | .var i => [i]
  | .lit _ | .pi => []
  | .neg a | .powi a _ | .sqrt a | .rpow a _ | .app _ a => a.vars
  | .add a b | .sub a b | .mul a b | .div a b => a.vars ++ b.vars

/-- Derivative along a direction in which variable `j` moves with velocity `v j`. -/
def dir (v : ℕ → Expr) : Expr → Expr
  | .var j => v j
  | .lit _ | .pi => .lit 0
  | .neg a => .neg (a.dir v)
  | .add a b => .add (a.dir v) (b.dir v)
  | .sub a b => .sub (a.dir v) (b.dir v)
  | .mul a b => .add (.mul (a.dir v) b) (.mul a (b.dir v))
  | .div a b => .div (.sub (.mul (a.dir v) b) (.mul a (b.dir v))) (.powi b 2)
  | .powi a n => .mul (.mul (.lit n) (.powi a (n - 1))) (a.dir v)
  | .sqrt a => .div (a.dir v) (.mul (.lit 2) (.sqrt a))
  | .rpow a q => .mul (.mul (.lit q) (.rpow a (q - 1))) (a.dir v)
  | .app .sin a => .mul (.app .cos a) (a.dir v)
  | .app .cos a => .mul (.neg (.app .sin a)) (a.dir v)
  | .app .exp a => .mul (.app .exp a) (a.dir v)
  | .app .log a => .div (a.dir v) a

/-- Where the differentiation rules apply. -/
def diffOK (env : ℕ → ℝ) : Expr → Prop
  | .var _ | .lit _ | .pi => True
  | .neg a => a.diffOK env
  | .add a b | .sub a b | .mul a b => a.diffOK env ∧ b.diffOK env
  | .div a b => a.diffOK env ∧ b.diffOK env ∧ b.eval env ≠ 0
  | .powi a n => a.diffOK env ∧ (0 ≤ n ∨ a.eval env ≠ 0)
  | .sqrt a => a.diffOK env ∧ a.eval env ≠ 0
  | .rpow a q => a.diffOK env ∧ (1 ≤ q ∨ a.eval env ≠ 0)
  | .app .log a => a.diffOK env ∧ a.eval env ≠ 0
  | .app _ a => a.diffOK env

/-- Unit velocity in coordinate `i`. -/
def basis (i : ℕ) : ℕ → Expr := fun j => if j = i then .lit 1 else .lit 0

/-- The partial derivative `∂e/∂x_i`. -/
def deriv (i : ℕ) (e : Expr) : Expr := e.dir (basis i)

/-- **Chain rule.** If every variable `j` of `e` moves along `γ j` with velocity
`(v j).eval (γ t)`, and `e.diffOK (γ t)`, then `(e.dir v).eval (γ t)` is the derivative of
`s ↦ e.eval (γ s)` at `t`. -/
theorem hasDerivAt_dir (v : ℕ → Expr) (γ : ℕ → ℝ → ℝ) (t : ℝ) :
    ∀ e : Expr, (∀ j ∈ e.vars, HasDerivAt (γ j) ((v j).eval (fun i => γ i t)) t) →
      e.diffOK (fun i => γ i t) →
      HasDerivAt (fun s => e.eval (fun i => γ i s)) ((e.dir v).eval (fun i => γ i t)) t
  | .var j, hγ, _ => by simpa [eval, dir] using hγ j (by simp [vars])
  | .lit q, _, _ => by simpa [eval, dir] using hasDerivAt_const t (q : ℝ)
  | .pi, _, _ => by simpa [eval, dir] using hasDerivAt_const t Real.pi
  | .neg a, hγ, h => by
      simpa [eval, dir] using (hasDerivAt_dir v γ t a hγ h).neg
  | .add a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      exact (hasDerivAt_dir v γ t a (fun j hj => hγ j (.inl hj)) h.1).add
        (hasDerivAt_dir v γ t b (fun j hj => hγ j (.inr hj)) h.2)
  | .sub a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      exact (hasDerivAt_dir v γ t a (fun j hj => hγ j (.inl hj)) h.1).sub
        (hasDerivAt_dir v γ t b (fun j hj => hγ j (.inr hj)) h.2)
  | .mul a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      exact (hasDerivAt_dir v γ t a (fun j hj => hγ j (.inl hj)) h.1).mul
        (hasDerivAt_dir v γ t b (fun j hj => hγ j (.inr hj)) h.2)
  | .div a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      have := (hasDerivAt_dir v γ t a (fun j hj => hγ j (.inl hj)) h.1).div
        (hasDerivAt_dir v γ t b (fun j hj => hγ j (.inr hj)) h.2.1) h.2.2
      simpa [eval, dir] using this
  | .powi a n, hγ, h => by
      have ha := hasDerivAt_dir v γ t a hγ h.1
      have := (hasDerivAt_zpow n (a.eval fun i => γ i t) h.2.symm).comp t ha
      simpa [eval, dir, Function.comp_def] using this
  | .sqrt a, hγ, h => by
      simpa [eval, dir] using (hasDerivAt_dir v γ t a hγ h.1).sqrt h.2
  | .rpow a q, hγ, h => by
      have ha := hasDerivAt_dir v γ t a hγ h.1
      have hq : (a.eval fun i => γ i t) ≠ 0 ∨ 1 ≤ (q : ℝ) :=
        h.2.symm.imp id (fun h1 => by exact_mod_cast h1)
      have := ha.rpow_const hq
      simp only [eval, dir]
      convert this using 1
      push_cast
      ring
  | .app .sin a, hγ, h => by
      simpa [eval, dir, Fn.eval] using (hasDerivAt_dir v γ t a hγ h).sin
  | .app .cos a, hγ, h => by
      simpa [eval, dir, Fn.eval] using (hasDerivAt_dir v γ t a hγ h).cos
  | .app .exp a, hγ, h => by
      simpa [eval, dir, Fn.eval] using (hasDerivAt_dir v γ t a hγ h).exp
  | .app .log a, hγ, h => by
      simpa [eval, dir, Fn.eval] using (hasDerivAt_dir v γ t a hγ h.1).log h.2

/-- **Partial derivatives.** Where `e.diffOK env` holds, `e.deriv i` evaluates to the
derivative of `e` in its `i`-th argument. -/
theorem hasDerivAt_deriv (i : ℕ) (e : Expr) (env : ℕ → ℝ) (h : e.diffOK env) :
    HasDerivAt (fun x => e.eval (Function.update env i x)) ((e.deriv i).eval env) (env i) := by
  have hγ : ∀ j ∈ e.vars, HasDerivAt (fun s => Function.update env i s j)
      ((basis i j).eval (fun k => Function.update env i (env i) k)) (env i) := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa [basis, eval] using hasDerivAt_id (env j)
    · simpa [basis, eval, hj] using hasDerivAt_const (env i) (env j)
  have := hasDerivAt_dir (basis i) (fun j s => Function.update env i s j) (env i) e hγ
    (by simpa using h)
  simpa [deriv] using this

/-- The derivative mentions no variables beyond those of `e` and of the velocities. -/
theorem vars_dir (v : ℕ → Expr) (P : ℕ → Prop) (hv : ∀ i, ∀ j ∈ (v i).vars, P j) :
    ∀ e : Expr, (∀ j ∈ e.vars, P j) → ∀ j ∈ (e.dir v).vars, P j
  | .var i, _ => by simpa [dir] using hv i
  | .lit _, _ => by simp [dir, vars]
  | .pi, _ => by simp [dir, vars]
  | .neg a, he => by simpa [dir, vars] using vars_dir v P hv a he
  | .add a b, he | .sub a b, he => by
      simp only [vars, List.mem_append] at he
      have := vars_dir v P hv a (fun j hj => he j (.inl hj))
      have := vars_dir v P hv b (fun j hj => he j (.inr hj))
      simp only [dir, vars, List.mem_append]; aesop
  | .mul a b, he | .div a b, he => by
      simp only [vars, List.mem_append] at he
      have := vars_dir v P hv a (fun j hj => he j (.inl hj))
      have := vars_dir v P hv b (fun j hj => he j (.inr hj))
      simp only [dir, vars, List.mem_append]; aesop
  | .powi a n, he | .rpow a n, he | .sqrt a, he => by
      have := vars_dir v P hv a he
      simp only [dir, vars, List.mem_append, List.not_mem_nil]; aesop
  | .app f a, he => by
      have := vars_dir v P hv a he
      cases f <;> simp only [dir, vars, List.mem_append, List.not_mem_nil] <;> aesop

theorem vars_deriv (i : ℕ) (e : Expr) (P : ℕ → Prop) (he : ∀ j ∈ e.vars, P j) :
    ∀ j ∈ (e.deriv i).vars, P j :=
  vars_dir (basis i) P (fun k j hj => by unfold basis at hj; split_ifs at hj <;> simp [vars] at hj)
    e he

/-- Evaluation is continuous along continuous curves wherever `diffOK` holds, and
`diffOK` then holds near `t` as well. -/
theorem continuousAt_eval (γ : ℕ → ℝ → ℝ) (t : ℝ) :
    ∀ e : Expr, (∀ j ∈ e.vars, ContinuousAt (γ j) t) → e.diffOK (fun i => γ i t) →
      ContinuousAt (fun s => e.eval (fun i => γ i s)) t ∧
        ∀ᶠ s in nhds t, e.diffOK (fun i => γ i s)
  | .var j, hγ, _ => ⟨by simpa [eval] using hγ j (by simp [vars]), by simp [diffOK]⟩
  | .lit q, _, _ => ⟨by simpa [eval] using continuousAt_const, by simp [diffOK]⟩
  | .pi, _, _ => ⟨by simpa [eval] using continuousAt_const, by simp [diffOK]⟩
  | .neg a, hγ, h => by
      obtain ⟨c, e⟩ := continuousAt_eval γ t a hγ h
      exact ⟨by simpa [eval] using c.neg, by simpa [diffOK] using e⟩
  | .add a b, hγ, h | .sub a b, hγ, h | .mul a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a (fun j hj => hγ j (.inl hj)) h.1
      obtain ⟨cb, eb⟩ := continuousAt_eval γ t b (fun j hj => hγ j (.inr hj)) h.2
      first
        | exact ⟨by simpa [eval] using ca.add cb, (ea.and eb).mono fun _ h => h⟩
        | exact ⟨by simpa [eval] using ca.sub cb, (ea.and eb).mono fun _ h => h⟩
        | exact ⟨by simpa [eval] using ca.mul cb, (ea.and eb).mono fun _ h => h⟩
  | .div a b, hγ, h => by
      simp only [vars, List.mem_append] at hγ
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a (fun j hj => hγ j (.inl hj)) h.1
      obtain ⟨cb, eb⟩ := continuousAt_eval γ t b (fun j hj => hγ j (.inr hj)) h.2.1
      exact ⟨by simpa [eval] using ca.div cb h.2.2,
        ((ea.and eb).and (cb.eventually_ne h.2.2)).mono fun _ h => ⟨h.1.1, h.1.2, h.2⟩⟩
  | .powi a n, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h.1
      refine ⟨by simpa [eval] using ca.zpow₀ n h.2.symm, ?_⟩
      rcases h.2 with hn | hn
      · exact ea.mono fun _ h => ⟨h, .inl hn⟩
      · exact (ea.and (ca.eventually_ne hn)).mono fun _ h => ⟨h.1, .inr h.2⟩
  | .sqrt a, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h.1
      exact ⟨by simpa [eval] using ca.sqrt,
        (ea.and (ca.eventually_ne h.2)).mono fun _ h => h⟩
  | .rpow a q, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h.1
      have hq : (a.eval fun i => γ i t) ≠ 0 ∨ 0 ≤ (q : ℝ) :=
        h.2.symm.imp id (fun h1 => by have : (1 : ℝ) ≤ q := by exact_mod_cast h1
                                      linarith)
      refine ⟨by simpa [eval] using ca.rpow_const hq, ?_⟩
      rcases h.2 with hn | hn
      · exact ea.mono fun _ h => ⟨h, .inl hn⟩
      · exact (ea.and (ca.eventually_ne hn)).mono fun _ h => ⟨h.1, .inr h.2⟩
  | .app .sin a, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h
      exact ⟨by simpa [eval, Fn.eval] using Real.continuous_sin.continuousAt.comp ca,
        by simpa [diffOK] using ea⟩
  | .app .cos a, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h
      exact ⟨by simpa [eval, Fn.eval] using Real.continuous_cos.continuousAt.comp ca,
        by simpa [diffOK] using ea⟩
  | .app .exp a, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h
      exact ⟨by simpa [eval, Fn.eval] using Real.continuous_exp.continuousAt.comp ca,
        by simpa [diffOK] using ea⟩
  | .app .log a, hγ, h => by
      obtain ⟨ca, ea⟩ := continuousAt_eval γ t a hγ h.1
      exact ⟨by simpa [eval, Fn.eval] using ca.log h.2,
        (ea.and (ca.eventually_ne h.2)).mono fun _ h => h⟩

end Expr
end PhysVerify
