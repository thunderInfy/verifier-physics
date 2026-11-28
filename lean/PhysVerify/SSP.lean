import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PhysVerify.Harten

/-!
# Strong-stability-preserving time stepping: a class theorem

An explicit Runge-Kutta method in Shu-Osher form has stages `u 0 = uⁿ` and, for `0 < i ≤ s`,

  `u i = Σ_{k < i} (α i k • u k + (Δt * β i k) • F (u k))`,

with `u s = uⁿ⁺¹`. If the forward-Euler step `v + t • F v` stays in a convex set `S` for every
`v ∈ S` and `0 ≤ t ≤ τ`, and the arrays are admissible (`α, β ≥ 0`, each row of `α` sums to 1,
`α i k = 0 → β i k = 0`), then every stage stays in `S` once `Δt * β i k ≤ α i k * τ` for all
`k < i`, that is `Δt ≤ c τ` with `c = min_{β i k > 0} α i k / β i k`. Each stage is a convex
combination of forward-Euler steps of length `Δt β i k / α i k ≤ τ` from earlier stages, so the
proof is an induction over the stages with `Convex.sum_mem`.

Nothing here is specific to a scheme: `S` is any convex set of any vector space over any
linearly ordered field `𝕜` (`ℚ` and `ℝ` both work), and `F` is any map, not even continuous.

* `ssp_stage_mem`: the lemma, with the step bound `Δt * β ≤ α * τ` written without division.
* `ssp_preserves_meaning`: the same with an SSP coefficient `c` (`c * β ≤ α`) and `Δt ≤ c * τ`;
  the claim kind `ssp_preserves` reads this way.
* `ssp_convexOn_le`: a convex functional that forward Euler does not increase is not increased
  by any stage (total variation, a norm, a convex entropy).
* `ssp_nonneg`, `ssp_bounds`: positivity and the global maximum principle on `ι → 𝕜`.
* `ssp_tvd`: TVD on the periodic grid, for `Harten.TV`, which is convex (`TV_convexOn`).
* `ssprk33_ratio`, `ssprk33_tvd`: the three-stage third-order method of the SSP literature,
  `c = 1`, as an instance.
-/

namespace PhysVerify.SSP

open Finset

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- An explicit `s`-stage method in Shu-Osher form; only `α i k`, `β i k` with `k < i ≤ s`
are read. -/
structure ShuOsher (𝕜 : Type*) where
  s : ℕ
  α : ℕ → ℕ → 𝕜
  β : ℕ → ℕ → 𝕜

namespace ShuOsher

/-- Non-negative arrays, rows of `α` summing to 1, and `β i k = 0` wherever `α i k = 0`. -/
def Admissible (m : ShuOsher 𝕜) : Prop :=
  (∀ i k, k < i → i ≤ m.s → 0 ≤ m.α i k ∧ 0 ≤ m.β i k ∧ (m.α i k = 0 → m.β i k = 0)) ∧
  ∀ i, 0 < i → i ≤ m.s → ∑ k ∈ range i, m.α i k = 1

/-- `c` is an SSP coefficient of the arrays: `c * β i k ≤ α i k` for every `k < i ≤ s`, that is
`c ≤ α i k / β i k` wherever `β i k > 0`. -/
def Ratio (m : ShuOsher 𝕜) (c : 𝕜) : Prop :=
  ∀ i k, k < i → i ≤ m.s → c * m.β i k ≤ m.α i k

variable [AddCommGroup E] [Module 𝕜 E]

/-- `u 0, ..., u s` are the stages of one step of length `dt` for the right-hand side `F`. -/
def Stages (m : ShuOsher 𝕜) (F : E → E) (dt : 𝕜) (u : ℕ → E) : Prop :=
  ∀ i, 0 < i → i ≤ m.s → u i = ∑ k ∈ range i, (m.α i k • u k + (dt * m.β i k) • F (u k))

end ShuOsher

variable [AddCommGroup E] [Module 𝕜 E]

/-- The forward-Euler step of length `t` stays in `S` for every `t ∈ [0, τ]`. -/
def FEInvariant (S : Set E) (F : E → E) (τ : 𝕜) : Prop :=
  ∀ v ∈ S, ∀ t : 𝕜, 0 ≤ t → t ≤ τ → v + t • F v ∈ S

/-- The convexity lemma: every stage stays in `S` when `dt * β i k ≤ α i k * τ`. -/
theorem ssp_stage_mem {S : Set E} (hS : Convex 𝕜 S) {F : E → E} {τ : 𝕜} (hFE : FEInvariant S F τ)
    {m : ShuOsher 𝕜} (hm : m.Admissible) {dt : 𝕜} (hdt : 0 ≤ dt)
    (hcfl : ∀ i k, k < i → i ≤ m.s → dt * m.β i k ≤ m.α i k * τ)
    {u : ℕ → E} (hu : m.Stages F dt u) (h0 : u 0 ∈ S) : ∀ i ≤ m.s, u i ∈ S := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact h0
    rw [hu i hpos hi]
    -- the k-th term is α i k • z k, with z k a forward-Euler step from u k (or u k itself)
    let z : ℕ → E := fun k =>
      if m.α i k = 0 then u k else u k + (dt * m.β i k / m.α i k) • F (u k)
    have hterm : ∀ k ∈ range i,
        m.α i k • u k + (dt * m.β i k) • F (u k) = m.α i k • z k := by
      intro k hk
      have hki : k < i := mem_range.mp hk
      by_cases h : m.α i k = 0
      · simp [z, h, (hm.1 i k hki hi).2.2 h]
      · have hc : m.α i k * (dt * m.β i k / m.α i k) = dt * m.β i k := by field_simp
        simp only [z]
        rw [if_neg h, smul_add, smul_smul, hc]
    rw [sum_congr rfl hterm]
    refine hS.sum_mem (fun k hk => (hm.1 i k (mem_range.mp hk) hi).1) (hm.2 i hpos hi) ?_
    intro k hk
    have hki : k < i := mem_range.mp hk
    have huk : u k ∈ S := ih k hki (by omega)
    obtain ⟨hα, hβ, -⟩ := hm.1 i k hki hi
    by_cases h : m.α i k = 0
    · simp only [z]
      rw [if_pos h]
      exact huk
    · have hpos' : 0 < m.α i k := lt_of_le_of_ne hα (Ne.symm h)
      simp only [z]
      rw [if_neg h]
      refine hFE _ huk _ (div_nonneg (mul_nonneg hdt hβ) hα) ?_
      rw [div_le_iff₀ hpos', mul_comm τ]
      exact hcfl i k hki hi

/-- The meaning of the claim kind `ssp_preserves`: with an SSP coefficient `c` of the arrays and
`0 ≤ dt ≤ c * τ`, every stage, the new step `u s` included, stays in `S`. -/
theorem ssp_preserves_meaning {S : Set E} (hS : Convex 𝕜 S) {F : E → E} {τ : 𝕜}
    (hτ : 0 ≤ τ) (hFE : FEInvariant S F τ) {m : ShuOsher 𝕜} (hm : m.Admissible) {c : 𝕜}
    (hc : m.Ratio c) {dt : 𝕜} (hdt : 0 ≤ dt) (hdtc : dt ≤ c * τ)
    {u : ℕ → E} (hu : m.Stages F dt u) (h0 : u 0 ∈ S) : ∀ i ≤ m.s, u i ∈ S := by
  refine ssp_stage_mem hS hFE hm hdt (fun i k hki hi => ?_) hu h0
  obtain ⟨-, hβ, -⟩ := hm.1 i k hki hi
  calc dt * m.β i k ≤ (c * τ) * m.β i k := mul_le_mul_of_nonneg_right hdtc hβ
    _ = τ * (c * m.β i k) := by ring
    _ ≤ τ * m.α i k := mul_le_mul_of_nonneg_left (hc i k hki hi) hτ
    _ = m.α i k * τ := by ring

/-- A convex functional `φ` that no forward-Euler step of length `t ∈ [0, τ]` increases is not
increased by any stage. -/
theorem ssp_convexOn_le {φ : E → 𝕜} (hφ : ConvexOn 𝕜 Set.univ φ) {F : E → E} {τ : 𝕜}
    (hτ : 0 ≤ τ) (hFE : ∀ v, ∀ t : 𝕜, 0 ≤ t → t ≤ τ → φ (v + t • F v) ≤ φ v)
    {m : ShuOsher 𝕜} (hm : m.Admissible) {c : 𝕜} (hc : m.Ratio c) {dt : 𝕜} (hdt : 0 ≤ dt)
    (hdtc : dt ≤ c * τ) {u : ℕ → E} (hu : m.Stages F dt u) : ∀ i ≤ m.s, φ (u i) ≤ φ (u 0) := by
  have hconv : Convex 𝕜 {x | φ x ≤ φ (u 0)} := by simpa using hφ.convex_le (φ (u 0))
  have key := ssp_preserves_meaning hconv hτ
    (fun v hv t ht0 ht => le_trans (hFE v t ht0 ht) hv) hm hc hdt hdtc hu (le_refl (φ (u 0)))
  exact fun i hi => key i hi

theorem convex_nonneg (ι : Type*) : Convex 𝕜 {v : ι → 𝕜 | ∀ j, 0 ≤ v j} := by
  intro x hx y hy a b ha hb _
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))

theorem convex_bounds (ι : Type*) (lo hi : 𝕜) :
    Convex 𝕜 {v : ι → 𝕜 | ∀ j, lo ≤ v j ∧ v j ≤ hi} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hx j).1 ha
  have h2 := mul_le_mul_of_nonneg_left (hy j).1 hb
  have h3 := mul_le_mul_of_nonneg_left (hx j).2 ha
  have h4 := mul_le_mul_of_nonneg_left (hy j).2 hb
  have elo : a * lo + b * lo = lo := by rw [← add_mul, hab, one_mul]
  have ehi : a * hi + b * hi = hi := by rw [← add_mul, hab, one_mul]
  constructor <;> linarith

/-- Positivity: if forward Euler keeps non-negative data non-negative for `t ∈ [0, τ]`, so does
every stage for `0 ≤ dt ≤ c * τ`. -/
theorem ssp_nonneg {ι : Type*} {F : (ι → 𝕜) → (ι → 𝕜)} {τ : 𝕜} (hτ : 0 ≤ τ)
    (hFE : ∀ v : ι → 𝕜, (∀ j, 0 ≤ v j) → ∀ t : 𝕜, 0 ≤ t → t ≤ τ → ∀ j, 0 ≤ v j + t * F v j)
    {m : ShuOsher 𝕜} (hm : m.Admissible) {c : 𝕜} (hc : m.Ratio c) {dt : 𝕜} (hdt : 0 ≤ dt)
    (hdtc : dt ≤ c * τ) {u : ℕ → ι → 𝕜} (hu : m.Stages F dt u) (h0 : ∀ j, 0 ≤ u 0 j) :
    ∀ i ≤ m.s, ∀ j, 0 ≤ u i j :=
  ssp_preserves_meaning (S := {v : ι → 𝕜 | ∀ j, 0 ≤ v j}) (convex_nonneg ι) hτ
    (fun v hv t ht0 ht => by simpa using hFE v hv t ht0 ht) hm hc hdt hdtc hu h0

/-- The global maximum principle: if forward Euler keeps data in `[lo, hi]` for `t ∈ [0, τ]`
(a local maximum principle gives this with `lo = min uⁿ`, `hi = max uⁿ`), so does every stage. -/
theorem ssp_bounds {ι : Type*} {F : (ι → 𝕜) → (ι → 𝕜)} {τ : 𝕜} (hτ : 0 ≤ τ) (lo hi : 𝕜)
    (hFE : ∀ v : ι → 𝕜, (∀ j, lo ≤ v j ∧ v j ≤ hi) → ∀ t : 𝕜, 0 ≤ t → t ≤ τ →
      ∀ j, lo ≤ v j + t * F v j ∧ v j + t * F v j ≤ hi)
    {m : ShuOsher 𝕜} (hm : m.Admissible) {c : 𝕜} (hc : m.Ratio c) {dt : 𝕜} (hdt : 0 ≤ dt)
    (hdtc : dt ≤ c * τ) {u : ℕ → ι → 𝕜} (hu : m.Stages F dt u)
    (h0 : ∀ j, lo ≤ u 0 j ∧ u 0 j ≤ hi) : ∀ i ≤ m.s, ∀ j, lo ≤ u i j ∧ u i j ≤ hi :=
  ssp_preserves_meaning (S := {v : ι → 𝕜 | ∀ j, lo ≤ v j ∧ v j ≤ hi}) (convex_bounds ι lo hi) hτ
    (fun v hv t ht0 ht => by simpa using hFE v hv t ht0 ht) hm hc hdt hdtc hu h0

variable {N : ℕ} [NeZero N]

/-- The periodic total variation is convex (it is a seminorm). -/
theorem TV_convexOn : ConvexOn 𝕜 Set.univ (Harten.TV (α := 𝕜) (N := N)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  simp only [Harten.TV, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  calc |a * x (i + 1) + b * y (i + 1) - (a * x i + b * y i)|
      = |a * (x (i + 1) - x i) + b * (y (i + 1) - y i)| := by congr 1; ring
    _ ≤ |a * (x (i + 1) - x i)| + |b * (y (i + 1) - y i)| := abs_add_le _ _
    _ = a * |x (i + 1) - x i| + b * |y (i + 1) - y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- TVD on the periodic grid: a forward-Euler step that is TVD for `t ∈ [0, τ]` gives TVD stages
for `0 ≤ dt ≤ c * τ`. -/
theorem ssp_tvd {F : (ZMod N → 𝕜) → (ZMod N → 𝕜)} {τ : 𝕜} (hτ : 0 ≤ τ)
    (hFE : ∀ v, ∀ t : 𝕜, 0 ≤ t → t ≤ τ → Harten.TV (v + t • F v) ≤ Harten.TV v)
    {m : ShuOsher 𝕜} (hm : m.Admissible) {c : 𝕜} (hc : m.Ratio c) {dt : 𝕜} (hdt : 0 ≤ dt)
    (hdtc : dt ≤ c * τ) {u : ℕ → ZMod N → 𝕜} (hu : m.Stages F dt u) :
    ∀ i ≤ m.s, Harten.TV (u i) ≤ Harten.TV (u 0) :=
  ssp_convexOn_le TV_convexOn hτ hFE hm hc hdt hdtc hu

/-- The three-stage third-order SSP method in Shu-Osher form:
`u1 = u0 + Δt F(u0)`, `u2 = 3/4 u0 + 1/4 (u1 + Δt F(u1))`, `u3 = 1/3 u0 + 2/3 (u2 + Δt F(u2))`. -/
def ssprk33 : ShuOsher 𝕜 where
  s := 3
  α := fun i k => match i, k with
    | 1, 0 => 1 | 2, 0 => 3 / 4 | 2, 1 => 1 / 4 | 3, 0 => 1 / 3 | 3, 2 => 2 / 3 | _, _ => 0
  β := fun i k => match i, k with
    | 1, 0 => 1 | 2, 1 => 1 / 4 | 3, 2 => 2 / 3 | _, _ => 0

theorem ssprk33_admissible : (ssprk33 : ShuOsher 𝕜).Admissible := by
  refine ⟨fun i k hki hi => ?_, fun i hi0 hi => ?_⟩
  · simp only [ssprk33] at hi ⊢
    interval_cases i <;> interval_cases k <;> norm_num
  · simp only [ssprk33] at hi ⊢
    interval_cases i <;> simp [sum_range_succ] <;> norm_num

theorem ssprk33_ratio : (ssprk33 : ShuOsher 𝕜).Ratio 1 := by
  intro i k hki hi
  simp only [ssprk33] at hi ⊢
  interval_cases i <;> interval_cases k <;> norm_num

/-- SSPRK(3,3) is TVD for `0 ≤ dt ≤ τ` whenever forward Euler is TVD for steps up to `τ`. -/
theorem ssprk33_tvd {F : (ZMod N → 𝕜) → (ZMod N → 𝕜)} {τ : 𝕜} (hτ : 0 ≤ τ)
    (hFE : ∀ v, ∀ t : 𝕜, 0 ≤ t → t ≤ τ → Harten.TV (v + t • F v) ≤ Harten.TV v)
    {dt : 𝕜} (hdt : 0 ≤ dt) (hdtτ : dt ≤ τ) {u : ℕ → ZMod N → 𝕜}
    (hu : (ssprk33 : ShuOsher 𝕜).Stages F dt u) : Harten.TV (u 3) ≤ Harten.TV (u 0) :=
  ssp_tvd hτ hFE ssprk33_admissible ssprk33_ratio hdt (by simpa using hdtτ) hu 3 le_rfl

end PhysVerify.SSP
