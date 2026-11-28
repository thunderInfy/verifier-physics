import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Harten's lemma: a theorem about a class of schemes

The scheme certificates (`PhysVerify.Scheme`) decide a property of one concrete scheme. The
theorems here quantify over the scheme's coefficients, so they hold for every scheme in a class.

Grid: the periodic grid `ZMod N`, any `N` with `[NeZero N]` (so `N = 1` and `N = 2` are
included; there `i + 1` and `i - 1` may coincide with `i` and nothing changes). Values lie in
any linearly ordered field `α`, so the same theorems apply over `ℚ` and `ℝ`.

Convention: both coefficients of interface `j + 1/2` (between cells `j` and `j + 1`) carry the
index `j`. A step in incremental form is

  `v i = u i + C i * (u (i+1) - u i) - D (i-1) * (u i - u (i-1))`

so `C i` plays `C_{i+1/2}` and `D (i-1)` plays `D_{i-1/2}`. Then, with `Δu_i = u (i+1) - u i`,

  `Δv_i = (1 - C i - D i) Δu_i + C (i+1) Δu_{i+1} + D (i-1) Δu_{i-1}`.

* `harten_tvd`: `0 ≤ C j`, `0 ≤ D j`, `C j + D j ≤ 1` for all `j` give `TV v ≤ TV u`.
* `harten_tvd_of_form`: the same for a scheme `H` whose coefficients may depend on the data.
* `linear_tvd`: `v i = a u(i-1) + b u i + c u(i+1)` with `a + b + c = 1`, `a, b, c ≥ 0`.
* `upwind_tvd`: first-order upwind, `0 ≤ ν ≤ 1`.
* `monotone_tvd`: a three-point conservative scheme whose update is nondecreasing in each
  argument is TVD (no Lipschitz bound is needed on a finite periodic grid: the difference
  quotients below are just numbers, with `x / 0 = 0` where the data are flat).
* `tvd_monotone_class_meaning`: every such scheme whose flux has difference quotients in stated
  bounds is TVD, for any class whose conditions imply `0 ≤ λ`, `0 ≤ λ aLo`, `λ bHi ≤ 0`,
  `λ (aHi - bLo) ≤ 1` (through `monotone3_of_bounds`).
* `tvd_limiter_class_meaning`: the flux-limited scheme is TVD for `0 ≤ ν ≤ νmax ≤ 1` and every
  limiter `φ` with `φ = 0` on `r ≤ 0` and `0 ≤ φ ≤ 2`, `νmax φ(r) ≤ 2r` on `r > 0`.
-/

namespace PhysVerify.Harten

open Finset

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {N : ℕ} [NeZero N]

/-- Total variation on the periodic grid: `TV u = Σ_i |u (i+1) - u i|`. -/
def TV (u : ZMod N → α) : α := ∑ i, |u (i + 1) - u i|

/-- One step in incremental form; `C i` is `C_{i+1/2}`, `D (i-1)` is `D_{i-1/2}`. -/
def hartenStep (u C D : ZMod N → α) (i : ZMod N) : α :=
  u i + C i * (u (i + 1) - u i) - D (i - 1) * (u i - u (i - 1))

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- A shift is a bijection of `ZMod N`, so it does not change a sum. -/
lemma sum_shift (f : ZMod N → α) : ∑ i, f (i + 1) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

omit [LinearOrder α] [IsStrictOrderedRing α] [NeZero N] in
lemma hartenStep_diff (u C D : ZMod N → α) (i : ZMod N) :
    hartenStep u C D (i + 1) - hartenStep u C D i =
      (1 - C i - D i) * (u (i + 1) - u i) + C (i + 1) * (u (i + 1 + 1) - u (i + 1))
        + D (i - 1) * (u i - u (i - 1)) := by
  simp only [hartenStep, add_sub_cancel_right]
  ring

lemma abs_comb_le {a b c x y z : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |a * x + b * y + c * z| ≤ a * |x| + b * |y| + c * |z| := by
  calc |a * x + b * y + c * z| ≤ |a * x + b * y| + |c * z| := abs_add_le _ _
    _ ≤ |a * x| + |b * y| + |c * z| := by gcongr; exact abs_add_le _ _
    _ = a * |x| + b * |y| + c * |z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc]

/-- **Harten's lemma** on the periodic grid. -/
theorem harten_tvd (u C D : ZMod N → α) (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    (hCD : ∀ j, C j + D j ≤ 1) : TV (hartenStep u C D) ≤ TV u := by
  have hpt : ∀ i, |hartenStep u C D (i + 1) - hartenStep u C D i| ≤
      (1 - C i - D i) * |u (i + 1) - u i| + C (i + 1) * |u (i + 1 + 1) - u (i + 1)|
        + D (i - 1) * |u i - u (i - 1)| := by
    intro i
    rw [hartenStep_diff]
    exact abs_comb_le (by linarith [hCD i]) (hC _) (hD _)
  have hCs : ∑ i, C (i + 1) * |u (i + 1 + 1) - u (i + 1)| = ∑ i, C i * |u (i + 1) - u i| :=
    sum_shift (fun i => C i * |u (i + 1) - u i|)
  have hDs : ∑ i, D (i - 1) * |u i - u (i - 1)| = ∑ i, D i * |u (i + 1) - u i| := by
    have h := sum_shift (fun i => D (i - 1) * |u i - u (i - 1)|)
    simp only [add_sub_cancel_right] at h
    exact h.symm
  unfold TV
  calc ∑ i, |hartenStep u C D (i + 1) - hartenStep u C D i|
      ≤ ∑ i, ((1 - C i - D i) * |u (i + 1) - u i| + C (i + 1) * |u (i + 1 + 1) - u (i + 1)|
          + D (i - 1) * |u i - u (i - 1)|) := sum_le_sum fun i _ => hpt i
    _ = ∑ i, ((1 - C i - D i) * |u (i + 1) - u i| + C i * |u (i + 1) - u i|
          + D i * |u (i + 1) - u i|) := by
      rw [sum_add_distrib, sum_add_distrib, hCs, hDs, ← sum_add_distrib, ← sum_add_distrib]
    _ = ∑ i, |u (i + 1) - u i| := sum_congr rfl fun i _ => by ring

/-- Harten's lemma for a scheme `H` that is in incremental form with data-dependent
coefficients `C u`, `D u`: if they meet the bounds for this `u`, one step does not raise TV. -/
theorem harten_tvd_of_form (H : (ZMod N → α) → (ZMod N → α)) (C D : (ZMod N → α) → ZMod N → α)
    (hform : ∀ u i, H u i = hartenStep u (C u) (D u) i) (u : ZMod N → α)
    (hC : ∀ j, 0 ≤ C u j) (hD : ∀ j, 0 ≤ D u j) (hCD : ∀ j, C u j + D u j ≤ 1) :
    TV (H u) ≤ TV u := by
  have : H u = hartenStep u (C u) (D u) := funext (hform u)
  rw [this]
  exact harten_tvd u (C u) (D u) hC hD hCD

/-- A linear three-point scheme `v i = a u(i-1) + b u i + c u(i+1)`. -/
def linStep (a b c : α) (u : ZMod N → α) (i : ZMod N) : α :=
  a * u (i - 1) + b * u i + c * u (i + 1)

/-- Corollary 1: with `a + b + c = 1` and `a, b, c ≥ 0` the linear scheme is TVD
(incremental form with `C i = c`, `D i = a`; the bound `a + c ≤ 1` is `b ≥ 0`). -/
theorem linear_tvd {a b c : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (u : ZMod N → α) : TV (linStep a b c u) ≤ TV u := by
  have hform : linStep a b c u = hartenStep u (fun _ => c) (fun _ => a) := by
    funext i
    have hb' : b = 1 - a - c := by linarith
    simp only [linStep, hartenStep, hb']
    ring
  rw [hform]
  exact harten_tvd u _ _ (fun _ => hc) (fun _ => ha) (fun _ => by linarith)

/-- First-order upwind for `u_t + a u_x = 0`, `a > 0`, Courant number `ν = a Δt / Δx`. -/
def upwindStep (ν : α) (u : ZMod N → α) (i : ZMod N) : α := u i - ν * (u i - u (i - 1))

/-- Corollary 2: upwind with `0 ≤ ν ≤ 1` is TVD (the linear scheme `a = ν, b = 1 - ν, c = 0`). -/
theorem upwind_tvd {ν : α} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (u : ZMod N → α) :
    TV (upwindStep ν u) ≤ TV u := by
  have hform : upwindStep ν u = linStep ν (1 - ν) 0 u := by
    funext i
    simp only [upwindStep, linStep]
    ring
  rw [hform]
  have hsum : ν + (1 - ν) + 0 = 1 := by ring
  exact linear_tvd h0 (by linarith) le_rfl hsum u

/-! ### Monotone three-point conservative schemes -/

/-- The update `H(a, b, c) = b - λ F(b, c) + λ F(a, b)` of a conservative scheme with numerical
flux `F` and `λ = Δt / Δx`. -/
def consH (F : α → α → α) (lam a b c : α) : α := b - lam * F b c + lam * F a b

/-- One step of the conservative scheme: `v i = H(u (i-1), u i, u (i+1))`. -/
def consStep (F : α → α → α) (lam : α) (u : ZMod N → α) (i : ZMod N) : α :=
  consH F lam (u (i - 1)) (u i) (u (i + 1))

/-- The scheme is monotone: `H` is nondecreasing in each argument. -/
def Monotone3 (F : α → α → α) (lam : α) : Prop :=
  ∀ a b c a' b' c', a ≤ a' → b ≤ b' → c ≤ c' → consH F lam a b c ≤ consH F lam a' b' c'

/-- `C j`: the part of the flux difference at `j + 1/2` from the jump in its right argument. -/
def fluxC (F : α → α → α) (lam : α) (u : ZMod N → α) (j : ZMod N) : α :=
  (lam * F (u j) (u j) - lam * F (u j) (u (j + 1))) / (u (j + 1) - u j)

/-- `D j`: the part of the flux difference at `j + 1/2` from the jump in its left argument. -/
def fluxD (F : α → α → α) (lam : α) (u : ZMod N → α) (j : ZMod N) : α :=
  (lam * F (u (j + 1)) (u (j + 1)) - lam * F (u j) (u (j + 1))) / (u (j + 1) - u j)

omit [IsStrictOrderedRing α] in
lemma div_mul_of_zero {x d : α} (h : d = 0 → x = 0) : x / d * d = x := by
  by_cases hd : d = 0
  · simp [hd, h hd]
  · exact div_mul_cancel₀ x hd

lemma div_nonneg_of_sign {x d : α} (hp : 0 < d → 0 ≤ x) (hn : d < 0 → x ≤ 0) : 0 ≤ x / d := by
  rcases lt_trichotomy d 0 with h | h | h
  · exact div_nonneg_of_nonpos (hn h) h.le
  · simp [h]
  · exact div_nonneg (hp h) h.le

lemma div_le_one_of_sign {x d : α} (hp : 0 < d → x ≤ d) (hn : d < 0 → d ≤ x) : x / d ≤ 1 := by
  rcases lt_trichotomy d 0 with h | h | h
  · exact (div_le_one_of_neg h).mpr (hn h)
  · simp [h]
  · exact (div_le_one h).mpr (hp h)

omit [NeZero N] in
lemma consStep_form (F : α → α → α) (lam : α) (u : ZMod N → α) (i : ZMod N) :
    consStep F lam u i = hartenStep u (fluxC F lam u) (fluxD F lam u) i := by
  have flat : ∀ j : ZMod N, u (j + 1) - u j = 0 → u (j + 1) = u j :=
    fun j h => sub_eq_zero.mp h
  have hC := div_mul_of_zero (x := lam * F (u i) (u i) - lam * F (u i) (u (i + 1)))
    (d := u (i + 1) - u i) (fun h => by rw [flat i h]; ring)
  have hD := div_mul_of_zero
    (x := lam * F (u (i - 1 + 1)) (u (i - 1 + 1)) - lam * F (u (i - 1)) (u (i - 1 + 1)))
    (d := u (i - 1 + 1) - u (i - 1)) (fun h => by rw [flat (i - 1) h]; ring)
  simp only [sub_add_cancel] at hD
  simp only [consStep, consH, hartenStep, fluxC, fluxD, sub_add_cancel]
  linear_combination hD - hC

/-- **Monotone ⇒ TVD** for a three-point conservative scheme on the periodic grid. -/
theorem monotone_tvd (F : α → α → α) (lam : α) (hmono : Monotone3 F lam) (u : ZMod N → α) :
    TV (consStep F lam u) ≤ TV u := by
  refine harten_tvd_of_form (consStep F lam) (fluxC F lam) (fluxD F lam)
    (consStep_form F lam) u (fun j => ?_) (fun j => ?_) (fun j => ?_)
  · -- `H` nondecreasing in `c`
    apply div_nonneg_of_sign
    · intro h
      have := hmono (u j) (u j) (u j) (u j) (u j) (u (j + 1)) le_rfl le_rfl (by linarith)
      simp only [consH] at this
      linarith
    · intro h
      have := hmono (u j) (u j) (u (j + 1)) (u j) (u j) (u j) le_rfl le_rfl (by linarith)
      simp only [consH] at this
      linarith
  · -- `H` nondecreasing in `a`
    apply div_nonneg_of_sign
    · intro h
      have := hmono (u j) (u (j + 1)) (u (j + 1)) (u (j + 1)) (u (j + 1)) (u (j + 1))
        (by linarith) le_rfl le_rfl
      simp only [consH] at this
      linarith
    · intro h
      have := hmono (u (j + 1)) (u (j + 1)) (u (j + 1)) (u j) (u (j + 1)) (u (j + 1))
        (by linarith) le_rfl le_rfl
      simp only [consH] at this
      linarith
  · -- `H` nondecreasing in `b`
    simp only [fluxC, fluxD, ← add_div]
    apply div_le_one_of_sign
    · intro h
      have := hmono (u j) (u j) (u (j + 1)) (u j) (u (j + 1)) (u (j + 1))
        le_rfl (by linarith) le_rfl
      simp only [consH] at this
      linarith
    · intro h
      have := hmono (u j) (u (j + 1)) (u (j + 1)) (u j) (u j) (u (j + 1))
        le_rfl (by linarith) le_rfl
      simp only [consH] at this
      linarith

/-! ### Classes of schemes: the scheme is a variable

The claim kinds `tvd_monotone_class` and `tvd_limiter_class` (physverify/schemes/harten_class.py)
state TVD for every scheme of a class given by conditions on its flux or its limiter. The theorems
below take the class as a predicate `K` and need only that `K` implies their hypotheses; the
checker decides that implication exactly. -/

/-- The flux's difference quotients in each argument lie in `[aLo, aHi]` and `[bLo, bHi]` (bounds
on `∂F/∂a`, `∂F/∂b` for a differentiable `F`, by the mean value theorem; here no derivative is
needed). -/
def FluxBounds (F : α → α → α) (aLo aHi bLo bHi : α) : Prop :=
  (∀ a a' b, a ≤ a' → aLo * (a' - a) ≤ F a' b - F a b ∧ F a' b - F a b ≤ aHi * (a' - a)) ∧
  (∀ a b b', b ≤ b' → bLo * (b' - b) ≤ F a b' - F a b ∧ F a b' - F a b ≤ bHi * (b' - b))

/-- Bounds on the difference quotients and a CFL relation make the scheme monotone. -/
theorem monotone3_of_bounds {F : α → α → α} {lam aLo aHi bLo bHi : α}
    (hF : FluxBounds F aLo aHi bLo bHi) (hl : 0 ≤ lam) (ha : 0 ≤ lam * aLo) (hb : lam * bHi ≤ 0)
    (hab : lam * (aHi - bLo) ≤ 1) : Monotone3 F lam := by
  intro a b c a' b' c' h1 h2 h3
  obtain ⟨hA, hB⟩ := hF
  have e1 := (hB b' c c' h3).2
  have e2 := (hA b b' c h2).2
  have e3 := (hA a a' b' h1).1
  have e4 := (hB a b b' h2).1
  have f1 := mul_le_mul_of_nonneg_left e1 hl
  have f2 := mul_le_mul_of_nonneg_left e2 hl
  have f3 := mul_le_mul_of_nonneg_left e3 hl
  have f4 := mul_le_mul_of_nonneg_left e4 hl
  have g1 := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h2)
  have g2 := mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr h3)
  have g3 := mul_nonneg ha (sub_nonneg.mpr h1)
  simp only [consH]
  nlinarith [f1, f2, f3, f4, g1, g2, g3]

/-- **Every monotone-flux scheme of a class is TVD.** If the conditions `K` on `(λ, aLo, aHi, bLo,
bHi)` imply `0 ≤ λ`, `0 ≤ λ aLo`, `λ bHi ≤ 0` and `λ (aHi - bLo) ≤ 1`, then every three-point
conservative scheme whose flux has difference quotients in those bounds is TVD. -/
theorem tvd_monotone_class_meaning {K : α → α → α → α → α → Prop}
    (hK : ∀ lam aLo aHi bLo bHi, K lam aLo aHi bLo bHi →
      0 ≤ lam ∧ 0 ≤ lam * aLo ∧ lam * bHi ≤ 0 ∧ lam * (aHi - bLo) ≤ 1)
    {F : α → α → α} {lam aLo aHi bLo bHi : α} (hk : K lam aLo aHi bLo bHi)
    (hF : FluxBounds F aLo aHi bLo bHi) (u : ZMod N → α) : TV (consStep F lam u) ≤ TV u := by
  obtain ⟨h1, h2, h3, h4⟩ := hK _ _ _ _ _ hk
  exact monotone_tvd F lam (monotone3_of_bounds hF h1 h2 h3 h4) u

/-- The smoothness ratio `r_j = Δu_{j-1} / Δu_j` (with `x / 0 = 0`). -/
def ratio (u : ZMod N → α) (j : ZMod N) : α := (u j - u (j - 1)) / (u (j + 1) - u j)

/-- `λ` times the flux-limited (Sweby) flux at `j + 1/2` for `u_t + a u_x = 0`, `a > 0`, Courant
number `ν`: upwind plus the limited anti-diffusive part, `ν u_j + ν(1-ν)/2 φ(r_j) Δu_j`. -/
def limFlux (φ : α → α) (ν : α) (u : ZMod N → α) (j : ZMod N) : α :=
  ν * u j + ν * (1 - ν) / 2 * (φ (ratio u j) * (u (j + 1) - u j))

/-- One step of the flux-limited scheme: `v i = u i - (G i - G (i-1))`, `G = λ F`. -/
def limStep (φ : α → α) (ν : α) (u : ZMod N → α) (i : ZMod N) : α :=
  u i - (limFlux φ ν u i - limFlux φ ν u (i - 1))

/-- Its incremental-form coefficient `D j` (`C = 0`). -/
def limD (φ : α → α) (ν : α) (u : ZMod N → α) (j : ZMod N) : α :=
  ν + ν * (1 - ν) / 2 *
    (φ (ratio u (j + 1)) * (u (j + 1 + 1) - u (j + 1)) / (u (j + 1) - u j) - φ (ratio u j))

omit [NeZero N] in
lemma limStep_form (φ : α → α) (hφ0 : φ 0 = 0) (ν : α) (u : ZMod N → α) (i : ZMod N) :
    limStep φ ν u i = hartenStep u (fun _ => 0) (limD φ ν u) i := by
  have hq := div_mul_of_zero (x := φ (ratio u (i - 1 + 1)) * (u (i - 1 + 1 + 1) - u (i - 1 + 1)))
    (d := u (i - 1 + 1) - u (i - 1)) (fun h => by
      have : ratio u (i - 1 + 1) = 0 := by simp only [ratio, add_sub_cancel_right, h, zero_div]
      rw [this, hφ0, zero_mul])
  simp only [sub_add_cancel] at hq
  simp only [limStep, limFlux, hartenStep, limD, sub_add_cancel]
  linear_combination (ν * (1 - ν) / 2) * hq

omit [NeZero N] in
lemma lim_q_bounds {φ : α → α} {νmax : α} (hneg : ∀ r ≤ 0, φ r = 0)
    (hpos : ∀ r, 0 < r → 0 ≤ φ r ∧ φ r ≤ 2 ∧ νmax * φ r ≤ 2 * r) (u : ZMod N → α) (j : ZMod N) :
    0 ≤ φ (ratio u (j + 1)) * (u (j + 1 + 1) - u (j + 1)) / (u (j + 1) - u j) ∧
      νmax * (φ (ratio u (j + 1)) * (u (j + 1 + 1) - u (j + 1)) / (u (j + 1) - u j)) ≤ 2 := by
  have hr : ratio u (j + 1) = (u (j + 1) - u j) / (u (j + 1 + 1) - u (j + 1)) := by
    simp only [ratio, add_sub_cancel_right]
  rw [hr]
  set a := u (j + 1) - u j
  set b := u (j + 1 + 1) - u (j + 1)
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb, hneg 0 le_rfl]
  have hq : φ (a / b) * b / a = φ (a / b) / (a / b) := (div_div_eq_mul_div _ _ _).symm
  rw [hq]
  rcases le_or_gt (a / b) 0 with h | h
  · simp [hneg _ h]
  · obtain ⟨p0, -, p2⟩ := hpos _ h
    refine ⟨div_nonneg p0 h.le, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ h]
    linarith

lemma lim_p_bounds {φ : α → α} {νmax : α} (hneg : ∀ r ≤ 0, φ r = 0)
    (hpos : ∀ r, 0 < r → 0 ≤ φ r ∧ φ r ≤ 2 ∧ νmax * φ r ≤ 2 * r) (r : α) : 0 ≤ φ r ∧ φ r ≤ 2 := by
  rcases le_or_gt r 0 with h | h
  · rw [hneg r h]; norm_num
  · exact ⟨(hpos r h).1, (hpos r h).2.1⟩

/-- **Every flux-limited scheme of a class is TVD.** If the conditions `K` on the limiter imply
`φ r = 0` for `r ≤ 0` and `0 ≤ φ r ≤ 2`, `νmax φ r ≤ 2 r` for `r > 0` (Sweby's region
`0 ≤ φ ≤ min(2r, 2)` when `νmax = 1`), with `νmax ≤ 1`, then the scheme with any limiter in the
class is TVD for every `ν ∈ [0, νmax]`. -/
theorem tvd_limiter_class_meaning {K : (α → α) → Prop} {νmax : α} (hm : νmax ≤ 1)
    (hK : ∀ φ, K φ → (∀ r ≤ 0, φ r = 0) ∧ ∀ r, 0 < r → 0 ≤ φ r ∧ φ r ≤ 2 ∧ νmax * φ r ≤ 2 * r)
    {φ : α → α} (hφ : K φ) {ν : α} (h0 : 0 ≤ ν) (h1 : ν ≤ νmax) (u : ZMod N → α) :
    TV (limStep φ ν u) ≤ TV u := by
  obtain ⟨hneg, hpos⟩ := hK φ hφ
  have hform : limStep φ ν u = hartenStep u (fun _ => 0) (limD φ ν u) :=
    funext (limStep_form φ (hneg 0 le_rfl) ν u)
  rw [hform]
  have hk : 0 ≤ ν * (1 - ν) / 2 := by
    have : 0 ≤ 1 - ν := by linarith
    exact div_nonneg (mul_nonneg h0 this) (by norm_num)
  refine harten_tvd u _ _ (fun _ => le_rfl) (fun j => ?_) (fun j => ?_)
  · obtain ⟨q0, -⟩ := lim_q_bounds hneg hpos u j
    obtain ⟨-, p2⟩ := lim_p_bounds hneg hpos (ratio u j)
    simp only [limD]
    nlinarith [mul_nonneg hk q0, mul_nonneg hk (sub_nonneg.mpr p2), sq_nonneg ν]
  · obtain ⟨q0, q2⟩ := lim_q_bounds hneg hpos u j
    obtain ⟨p0, -⟩ := lim_p_bounds hneg hpos (ratio u j)
    set q := φ (ratio u (j + 1)) * (u (j + 1 + 1) - u (j + 1)) / (u (j + 1) - u j)
    have hνq : ν * q ≤ 2 := le_trans (mul_le_mul_of_nonneg_right h1 q0) q2
    have h1ν : 0 ≤ (1 - ν) / 2 := by linarith
    have f := mul_le_mul_of_nonneg_left hνq h1ν
    simp only [limD]
    nlinarith [mul_nonneg hk p0, f]

end PhysVerify.Harten
