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

end PhysVerify.Harten
