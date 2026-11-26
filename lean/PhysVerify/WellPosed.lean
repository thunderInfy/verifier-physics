import PhysVerify.Expr
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Well-posedness contracts (step 4)

`Expr.Safe env e` lists the side conditions (non-zero denominators, `sqrt`/`log`/`rpow`
arguments away from 0, …) under which `e` is C¹ at `env`. For an autonomous system
`x' = F(x)` whose right-hand sides are `Safe` at `x₀`, Mathlib's Picard–Lindelöf and
Grönwall results give local existence and uniqueness of trajectories. Numerical tools
(step 5) rely on exactly this: their trajectory enclosures are only meaningful because
the solution exists and is unique.
-/

open Set Filter Topology

namespace PhysVerify

/-- Read the first `n` slots of an environment from a state vector. -/
noncomputable def ext (n : ℕ) (x : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then x ⟨i, h⟩ else 0

def Expr.Safe (env : ℕ → ℝ) : Expr → Prop
  | .var _ | .lit _ | .pi => True
  | .neg a => a.Safe env
  | .add a b | .sub a b | .mul a b => a.Safe env ∧ b.Safe env
  | .div a b => a.Safe env ∧ b.Safe env ∧ b.eval env ≠ 0
  | .powi a n => a.Safe env ∧ (a.eval env ≠ 0 ∨ 0 ≤ n)
  | .sqrt a | .rpow a _ => a.Safe env ∧ a.eval env ≠ 0
  | .app .log a => a.Safe env ∧ a.eval env ≠ 0
  | .app _ a => a.Safe env

theorem Expr.contDiffAt {n : ℕ} (x : Fin n → ℝ) :
    ∀ e : Expr, e.Safe (ext n x) → ContDiffAt ℝ 1 (fun y => e.eval (ext n y)) x
  | .var i, _ => by
      simp only [Expr.eval, ext]
      split_ifs with h
      · exact (contDiff_apply ℝ ℝ (⟨i, h⟩ : Fin n)).contDiffAt
      · exact contDiffAt_const
  | .lit _, _ => contDiffAt_const
  | .pi, _ => contDiffAt_const
  | .neg a, h => (a.contDiffAt x h).neg
  | .add a b, h => (a.contDiffAt x h.1).add (b.contDiffAt x h.2)
  | .sub a b, h => (a.contDiffAt x h.1).sub (b.contDiffAt x h.2)
  | .mul a b, h => (a.contDiffAt x h.1).mul (b.contDiffAt x h.2)
  | .div a b, h => (a.contDiffAt x h.1).div (b.contDiffAt x h.2.1) h.2.2
  | .powi a m, h => by
      have ha := a.contDiffAt x h.1
      simp only [Expr.eval]
      rcases le_or_gt 0 m with hm | hm
      · lift m to ℕ using hm
        simpa using ha.pow m
      · have hne : a.eval (ext n x) ≠ 0 := h.2.resolve_right (not_le.mpr hm)
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
        simpa [zpow_neg] using (ha.pow k).inv (pow_ne_zero k hne)
  | .sqrt a, h => (a.contDiffAt x h.1).sqrt h.2
  | .rpow a _, h => (a.contDiffAt x h.1).rpow_const_of_ne h.2
  | .app .sin a, h => Real.contDiff_sin.contDiffAt.comp x (a.contDiffAt x h)
  | .app .cos a, h => Real.contDiff_cos.contDiffAt.comp x (a.contDiffAt x h)
  | .app .exp a, h => Real.contDiff_exp.contDiffAt.comp x (a.contDiffAt x h)
  | .app .log a, h => (a.contDiffAt x h.1).log h.2

/-- Vector field of the autonomous system `xᵢ' = rhsᵢ(x)`. -/
noncomputable def field {n : ℕ} (rhs : Fin n → Expr) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (rhs i).eval (ext n x)

theorem field_contDiffAt {n : ℕ} {rhs : Fin n → Expr} {x : Fin n → ℝ}
    (h : ∀ i, (rhs i).Safe (ext n x)) : ContDiffAt ℝ 1 (field rhs) x :=
  contDiffAt_pi.2 fun i => (rhs i).contDiffAt x (h i)

/-- **Local existence.** -/
theorem wellPosed_exists {n : ℕ} {rhs : Fin n → Expr} {x₀ : Fin n → ℝ}
    (h : ∀ i, (rhs i).Safe (ext n x₀)) (t₀ : ℝ) :
    ∃ α : ℝ → Fin n → ℝ, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (field rhs (α t)) t :=
  (field_contDiffAt h).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- **Local uniqueness.** Two trajectories through the same safe state agree near `t₀`. -/
theorem wellPosed_unique {n : ℕ} {rhs : Fin n → Expr} {x₀ : Fin n → ℝ}
    (h : ∀ i, (rhs i).Safe (ext n x₀)) {t₀ : ℝ} {α β : ℝ → Fin n → ℝ}
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (field rhs (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (field rhs (β t)) t)
    (hα0 : α t₀ = x₀) (hβ0 : β t₀ = x₀) : α =ᶠ[𝓝 t₀] β := by
  obtain ⟨K, s, hs, hl⟩ := (field_contDiffAt h).exists_lipschitzOnWith
  have hαs : ∀ᶠ t in 𝓝 t₀, α t ∈ s :=
    hα.self_of_nhds.continuousAt.preimage_mem_nhds (hα0 ▸ hs)
  have hβs : ∀ᶠ t in 𝓝 t₀, β t ∈ s :=
    hβ.self_of_nhds.continuousAt.preimage_mem_nhds (hβ0 ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ => field rhs) (s := fun _ => s)
    (Eventually.of_forall fun _ => hl) (hα.and hαs) (hβ.and hβs) (hα0.trans hβ0.symm)

end PhysVerify
