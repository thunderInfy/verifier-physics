import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Defs
-- tactics the scheme certificates use
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhysVerify.Harten

/-!
# Discrete schemes: the general theorems behind the scheme certificates

The judge (`physverify/schemes/lean_cert.py`) writes one statement per exact verdict from the
spec, as a plain real expression in the stencil values; the certificate only has to prove a
pointwise fact (an identity by `ring`, or a sign condition), and the theorems here carry the
rest once:

* `conserves_of_telescoping`: an update with `H - u_i = Φ(i + 1/2) - Φ(i - 1/2)` conserves the
  total on every periodic grid `Fin (n + 1)`, of any length `n + 1 ≥ 1`.
* `NonnegComb.step_nonneg`, `NonnegComb.max_principle`: a non-negative combination of the
  stencil values preserves `u ≥ 0`, and if the weights sum to 1 it lies between the stencil's
  minimum and maximum.
* `nonneg_of_bernstein`: a polynomial with non-negative Bernstein coefficients on `[lo, hi]` is
  `≥ 0` there (the certificate proves the Bernstein identity by `ring`).
* `farkas`: atoms `≥ 0`, multipliers `≥ 0` and the identity `p = r + Σ μⱼ aⱼ` give `p ≥ 0`;
  with polynomial multipliers `μⱼ(ν)` their signs come from `nonneg_of_bernstein`.
* `tvd_of_incremental`: an update in Harten's incremental form with `C, D ≥ 0` and
  `C_{j+1/2} + D_{j+1/2} ≤ 1` is `TVD`, through `Harten.harten_tvd_of_form`.

States are vectors `Fin m → ℝ` (m = 1 for a scalar law), so systems use the same theorems. A
stencil is five cells wide (`u_{i-2}, …, u_{i+2}`); a three-point update ignores the outer two.
-/

namespace PhysVerify.Scheme

open Finset

/-- The total change `Σ_i g(u_{i-2}, …, u_{i+2})` over the periodic grid `Fin (n + 1)`. -/
def stepSum {α : Type*} (g : α → α → α → α → α → ℝ) (n : ℕ) (u : Fin (n + 1) → α) : ℝ :=
  ∑ i, g (u (i - 1 - 1)) (u (i - 1)) (u i) (u (i + 1)) (u (i + 1 + 1))

/-- Conservation: on every periodic grid whose cells all lie in the domain `D`, the changes
`g = H - u_i` sum to 0. -/
def Conserves {α : Type*} (D : α → Prop) (g : α → α → α → α → α → ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin (n + 1) → α), (∀ i, D (u i)) → stepSum g n u = 0

theorem sum_shift {β : Type*} [AddCommMonoid β] (n : ℕ) (f : Fin (n + 1) → β) (k : Fin (n + 1)) :
    ∑ i, f (i + k) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight k) _ _ (fun _ => rfl)

/-- The one theorem that carries conservation: a pointwise telescoping identity on the domain
implies conservation on every periodic grid. -/
theorem conserves_of_telescoping {α : Type*} {D : α → Prop} {g : α → α → α → α → α → ℝ}
    (Φ : α → α → α → α → ℝ)
    (h : ∀ a b c d e, D a → D b → D c → D d → D e → g a b c d e = Φ b c d e - Φ a b c d) :
    Conserves D g := by
  intro n u hu
  unfold stepSum
  rw [Finset.sum_congr rfl (fun i _ => h _ _ _ _ _ (hu _) (hu _) (hu _) (hu _) (hu _)),
    Finset.sum_sub_distrib, sub_eq_zero]
  rw [← sum_shift n (fun i => Φ (u (i - 1 - 1)) (u (i - 1)) (u i) (u (i + 1))) 1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [add_sub_cancel_right]

/-! ## One step on the periodic grid, total variation, local maximum principle

These carry the meaning of the refuted limiter claims; a refutation is a concrete periodic
state checked by `norm_num`. -/

/-- One step of the update `H` (a function of the stencil `u_{i-2}, …, u_{i+2}`). -/
def step (H : (Fin 5 → ℝ) → ℝ) {n : ℕ} [NeZero n] (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => H ![u (i - 1 - 1), u (i - 1), u i, u (i + 1), u (i + 1 + 1)]

/-- The total variation `Σ_i |u_{i+1} - u_i|` of a periodic state. -/
def TV {n : ℕ} [NeZero n] (u : Fin n → ℝ) : ℝ := ∑ i, |u (i + 1) - u i|

/-- TVD: one step never increases the total variation, on any periodic grid of `n ≥ 1` cells. -/
def TVD (H : (Fin 5 → ℝ) → ℝ) : Prop := ∀ (n : ℕ) [NeZero n] (u : Fin n → ℝ), TV (step H u) ≤ TV u

/-- The local maximum principle: `H` lies between any bounds of its stencil values. -/
def LocalMaxPrinciple (H : (Fin 5 → ℝ) → ℝ) : Prop :=
  ∀ (w : Fin 5 → ℝ) (m M : ℝ), (∀ k, m ≤ w k ∧ w k ≤ M) → m ≤ H w ∧ H w ≤ M

/-- `H` is non-decreasing in every stencil value (five-point schemes, whose CFL bound is on `lam` only). -/
def MonotoneVec (H : (Fin 5 → ℝ) → ℝ) : Prop := ∀ w w' : Fin 5 → ℝ, (∀ k, w k ≤ w' k) → H w ≤ H w'

/-- The two cases of `|t| = √(t²)`, the form in which `abs`, `min`, `max` and `minmod` reach the
statements, for a square root a certificate has named `s` (by `generalize`); it then splits on them
and argues linearly. -/
theorem sqrt_sq_cases {t s : ℝ} (e : Real.sqrt (t ^ 2) = s) : (s = t ∧ 0 ≤ t) ∨ (s = -t ∧ t < 0) := by
  subst e
  rcases le_or_gt 0 t with h | h
  · exact Or.inl ⟨Real.sqrt_sq h, h⟩
  · exact Or.inr ⟨by rw [Real.sqrt_sq_eq_abs, abs_of_neg h], h⟩

/-- **Harten's lemma for a stencil update.** If `H` is in incremental form,
`H(w) = w₂ + C(w) (w₃ - w₂) - D(w) (w₂ - w₁)`, with `C, D ≥ 0` for every stencil and
`C_{j+1/2} + D_{j+1/2} ≤ 1`, where `C_{j+1/2}` comes from the stencil of cell `j` and `D_{j+1/2}`
from that of cell `j + 1` (so the bound reads a six-point window), then `H` is TVD on every
periodic grid. `C` and `D` are any functions of the stencil (a certificate supplies them); the proof
is `Harten.harten_tvd_of_form` on `ZMod (k + 1)`, which is `Fin (k + 1)`. -/
theorem tvd_of_incremental (H : (Fin 5 → ℝ) → ℝ) (C D : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hform : ∀ w : Fin 5 → ℝ, H w = w 2 + C (w 0) (w 1) (w 2) (w 3) (w 4) * (w 3 - w 2)
      - D (w 0) (w 1) (w 2) (w 3) (w 4) * (w 2 - w 1))
    (hC : ∀ a b c d e, 0 ≤ C a b c d e) (hD : ∀ a b c d e, 0 ≤ D a b c d e)
    (hCD : ∀ a b c d e f, C a b c d e + D b c d e f ≤ 1) : TVD H := by
  intro n _ u
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let v : ZMod (k + 1) → ℝ := u
  let st : (ZMod (k + 1) → ℝ) → ZMod (k + 1) → Fin 5 → ℝ :=
    fun u i => ![u (i - 1 - 1), u (i - 1), u i, u (i + 1), u (i + 1 + 1)]
  let Cg : (ZMod (k + 1) → ℝ) → ZMod (k + 1) → ℝ :=
    fun u j => C (u (j - 1 - 1)) (u (j - 1)) (u j) (u (j + 1)) (u (j + 1 + 1))
  let Dg : (ZMod (k + 1) → ℝ) → ZMod (k + 1) → ℝ :=
    fun u j => D (u (j - 1)) (u j) (u (j + 1)) (u (j + 1 + 1)) (u (j + 1 + 1 + 1))
  have key := Harten.harten_tvd_of_form (N := k + 1) (α := ℝ) (fun u i => H (st u i)) Cg Dg
    (fun u i => by
      simp only [Harten.hartenStep, Cg, Dg, sub_add_cancel]
      rw [hform]
      simp [st])
    v (fun j => hC _ _ _ _ _) (fun j => hD _ _ _ _ _) (fun j => hCD _ _ _ _ _ _)
  exact key

/-- `H(um1, u0, up1)` is non-decreasing in each argument on the states satisfying `C`. -/
def MonotoneOn3 (C : ℝ → Prop) (H : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ a b c a' b' c', C a → C b → C c → C a' → C b' → C c' → a ≤ a' → b ≤ b' → c ≤ c' →
    H a b c ≤ H a' b' c'

/-! ## Linear schemes: non-negative combinations -/

/-- The stencil `u_{i-2}, …, u_{i+2}` as `w 0, …, w 4`. `H` is a non-negative combination of it. -/
def NonnegComb (H : (Fin 5 → ℝ) → ℝ) : Prop :=
  ∃ c : Fin 5 → ℝ, (∀ k, 0 ≤ c k) ∧ ∀ w, H w = ∑ k, c k * w k

/-- The unit state at stencil position `k`. -/
def unitVec (k : Fin 5) : Fin 5 → ℝ := fun j => if j = k then 1 else 0

/-- `NonnegComb` from five explicit weights (what a certificate supplies). -/
theorem nonnegComb_of {H : (Fin 5 → ℝ) → ℝ} (c0 c1 c2 c3 c4 : ℝ) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1)
    (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (hH : ∀ w, H w = c0 * w 0 + c1 * w 1 + c2 * w 2 + c3 * w 3 + c4 * w 4) : NonnegComb H := by
  refine ⟨![c0, c1, c2, c3, c4], fun k => ?_, fun w => ?_⟩
  · fin_cases k <;> simpa
  · rw [hH, Fin.sum_univ_five]; rfl

theorem NonnegComb.nonneg {H : (Fin 5 → ℝ) → ℝ} (hH : NonnegComb H) {w : Fin 5 → ℝ}
    (hw : ∀ k, 0 ≤ w k) : 0 ≤ H w := by
  obtain ⟨c, hc, he⟩ := hH
  rw [he]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) (hw k))

/-- Positivity on the periodic grid: `u ≥ 0` gives `u^{n+1} ≥ 0` in every cell. -/
theorem NonnegComb.step_nonneg {H : (Fin 5 → ℝ) → ℝ} (hH : NonnegComb H) (n : ℕ)
    (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (i : Fin (n + 1)) :
    0 ≤ H ![u (i - 1 - 1), u (i - 1), u i, u (i + 1), u (i + 1 + 1)] :=
  hH.nonneg (fun k => by fin_cases k <;> simp [hu])

/-- The maximum principle: if the weights sum to 1 (`H` maps the constant 1 to 1), the update
lies between the smallest and the largest stencil value. -/
theorem NonnegComb.max_principle {H : (Fin 5 → ℝ) → ℝ} (hH : NonnegComb H) (h1 : H (fun _ => 1) = 1) :
    LocalMaxPrinciple H := by
  intro w m M hw
  obtain ⟨c, hc, he⟩ := hH
  have hs : ∑ k, c k = 1 := by simpa [he] using h1
  rw [he]
  constructor
  · have : ∑ k, c k * m ≤ ∑ k, c k * w k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hw k).1 (hc k))
    rwa [← Finset.sum_mul, hs, one_mul] at this
  · have : ∑ k, c k * w k ≤ ∑ k, c k * M :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hw k).2 (hc k))
    rwa [← Finset.sum_mul, hs, one_mul] at this

/-- A negative weight refutes `NonnegComb`: `H (unit k)` is the weight of position `k`. -/
theorem not_nonnegComb {H : (Fin 5 → ℝ) → ℝ} (k : Fin 5) (hk : H (unitVec k) < 0) :
    ¬ NonnegComb H := by
  rintro ⟨c, hc, he⟩
  rw [he, Finset.sum_eq_single k (fun j _ hj => by simp [unitVec, hj]) (by simp)] at hk
  simp [unitVec] at hk
  linarith [hc k]

/-! ## Sign certificates -/

/-- `Σ_k b_k C(d, k) (x - lo)^k (hi - x)^(d - k)` with `d + 1` the length of `b`: the Bernstein
form on `[lo, hi]`, times `(hi - lo)^d`. -/
def bernsteinSum (lo hi x : ℝ) (b : List ℝ) : ℝ :=
  ∑ k : Fin b.length, b.get k * ((b.length - 1).choose k : ℝ) * (x - lo) ^ (k : ℕ) *
    (hi - x) ^ (b.length - 1 - k)

theorem bernsteinSum_nonneg {lo hi x : ℝ} {b : List ℝ} (hb : ∀ y ∈ b, 0 ≤ y) (h1 : lo ≤ x)
    (h2 : x ≤ hi) : 0 ≤ bernsteinSum lo hi x b := by
  unfold bernsteinSum
  refine Finset.sum_nonneg (fun k _ => ?_)
  have := hb _ (List.get_mem b k)
  have : 0 ≤ x - lo := by linarith
  have : 0 ≤ hi - x := by linarith
  positivity

/-- A polynomial with non-negative Bernstein coefficients on `[lo, hi]` is `≥ 0` there. The
certificate supplies the coefficients `b` and proves the identity `hid` (by `ring`). -/
theorem nonneg_of_bernstein {p lo hi x : ℝ} (b : List ℝ) (hlt : lo < hi) (hb : ∀ y ∈ b, 0 ≤ y)
    (h1 : lo ≤ x) (h2 : x ≤ hi) (hid : p * (hi - lo) ^ (b.length - 1) = bernsteinSum lo hi x b) :
    0 ≤ p := by
  have hpos : 0 < (hi - lo) ^ (b.length - 1) := pow_pos (by linarith) _
  have := bernsteinSum_nonneg hb h1 h2
  rw [← hid] at this
  exact nonneg_of_mul_nonneg_left this hpos

/-- The affine Farkas certificate: with atoms `aⱼ ≥ 0`, multipliers `μⱼ ≥ 0`, `r ≥ 0` and the
identity `p = r + Σ μⱼ aⱼ`, `p ≥ 0`. The certificate supplies `r` and `μ`; a wrong multiplier
breaks `hμ` or the identity `hid` (checked by `ring`). -/
theorem farkas {k : ℕ} {p : ℝ} (r : ℝ) (μ a : Fin k → ℝ) (hr : 0 ≤ r) (hμ : ∀ j, 0 ≤ μ j)
    (ha : ∀ j, 0 ≤ a j) (hid : p = r + ∑ j, μ j * a j) : 0 ≤ p := by
  rw [hid]
  exact add_nonneg hr (Finset.sum_nonneg (fun j _ => mul_nonneg (hμ j) (ha j)))

end PhysVerify.Scheme
