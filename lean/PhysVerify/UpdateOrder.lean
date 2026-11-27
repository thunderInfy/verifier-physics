import PhysVerify.Kernel
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Explicit update maps and kernels: `update_conserves_order_p`

`J` is conserved to order at least `p` by a one-step map `F` (an explicit map
`updateStep Phi`, or a straight-line kernel `exec prog`) when the per-step drift
`J(F z) − J(z)` is `O(h^(p+1))`. The step `h` is the variable with index `hi` (the judge
passes it; it is the position of `h` among `h` and the parameters, after the state).

Certificates (one pair for any map `F` with a junk-freeness predicate `OK`):

* `OrderVerified F OK D J R hi p`: `D` is non-empty and on `D`,
  `J(F z) − J(z) = h^(p+1) · R(z, h)` as an identity, with `R` junk-free there. The judge
  computes `R` exactly (polynomial division of the drift by `h^(p+1)`) and puts it in the
  statement; Lean proves the identity.
* `OrderRefuted F OK D J hi p`: a point `z` (state and parameters; its own `h` entry is
  ignored), a `k ≤ p` and a polynomial `S` with `S(z, 0) ≠ 0`, such that for every small
  `t > 0`, `z` with `h := t` is in `D` and `J(F z_t) − J(z_t) = t^k · S(z, t)`.

Main results:

* `order_drift_le` (per step): on every set where `|R| ≤ M`,
  `|J(F z) − J(z)| ≤ M · |h|^(p+1)`.
* `order_drift_compact`: if `R` is a polynomial (`Expr.isPoly`), it is continuous, so on every
  compact set of environments some `M` works.
* `order_refuted_lower`: at the certificate's `z`, `|J(F z_t) − J(z_t)| ≥ c · t^k` for all
  `t ∈ (0, δ)`, with `c > 0`.
* `order_refuted_meaning`: at that `z`, the drift is not `O(t^(p+1))` as `t → 0⁺`.

`update_order_meaning`, `update_order_refuted_meaning` and the `kernel_` versions are these
for `F = updateStep Phi` and `F = exec prog`.

Nothing here is about orbits. A bound on the drift accumulated over `N = T/h` steps would need
every point of the orbit to stay in a set where `R` is bounded, which Lean does not know for
these maps; that global statement is deliberately left out.
-/

namespace PhysVerify
open Expr Filter Topology

/-- Polynomial expressions: variables, rational literals, `+`, `−`, `×`, negation and powers
with a non-negative exponent. -/
def Expr.isPoly : Expr → Bool
  | .var _ | .lit _ => true
  | .neg a => a.isPoly
  | .add a b | .sub a b | .mul a b => a.isPoly && b.isPoly
  | .powi a n => a.isPoly && decide (0 ≤ n)
  | _ => false

/-- A polynomial expression is a continuous function of the environment (product topology). -/
theorem Expr.continuous_eval_of_isPoly :
    ∀ e : Expr, e.isPoly = true → Continuous fun env : ℕ → ℝ => e.eval env
  | .var i, _ => continuous_apply i
  | .lit _, _ => continuous_const
  | .neg a, h => (a.continuous_eval_of_isPoly h).neg
  | .add a b, h => by
      simp only [Expr.isPoly, Bool.and_eq_true] at h
      exact (a.continuous_eval_of_isPoly h.1).add (b.continuous_eval_of_isPoly h.2)
  | .sub a b, h => by
      simp only [Expr.isPoly, Bool.and_eq_true] at h
      exact (a.continuous_eval_of_isPoly h.1).sub (b.continuous_eval_of_isPoly h.2)
  | .mul a b, h => by
      simp only [Expr.isPoly, Bool.and_eq_true] at h
      exact (a.continuous_eval_of_isPoly h.1).mul (b.continuous_eval_of_isPoly h.2)
  | .powi a n, h => by
      simp only [Expr.isPoly, Bool.and_eq_true, decide_eq_true_eq] at h
      have he : (fun env : ℕ → ℝ => (Expr.powi a n).eval env) =
          fun env => a.eval env ^ n.toNat := by
        funext env
        simp only [Expr.eval]
        rw [← zpow_natCast, Int.toNat_of_nonneg h.2]
      rw [he]
      exact (a.continuous_eval_of_isPoly h.1).pow _
  | .pi, h | .div _ _, h | .sqrt _, h | .rpow _ _, h | .app _ _, h => by simp [Expr.isPoly] at h

/-- The per-step drift of `J` under the map `F`. -/
noncomputable def drift (F : (ℕ → ℝ) → (ℕ → ℝ)) (J : Expr) (env : ℕ → ℝ) : ℝ :=
  J.eval (F env) - J.eval env

/-- What a `VERIFIED` `update_conserves_order_p` certificate proves: on `D`,
`J(F z) − J(z) = h^(p+1) · R` with `h = env hi`; `D` is non-empty. -/
def OrderVerified (F : (ℕ → ℝ) → (ℕ → ℝ)) (OK : (ℕ → ℝ) → Prop) (D : (ℕ → ℝ) → Prop)
    (J R : Expr) (hi p : ℕ) : Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → OK env ∧ R.physOK env ∧ drift F J env = env hi ^ (p + 1) * R.eval env

/-- What a `REFUTED` `update_conserves_order_p` certificate proves: at a point `env`, with
`h := t` for every small `t > 0`, the point is in `D`, junk-free, and the drift is
`t^k · S(t)` with `k ≤ p` and `S(0) ≠ 0`, `S` a polynomial. -/
def OrderRefuted (F : (ℕ → ℝ) → (ℕ → ℝ)) (OK : (ℕ → ℝ) → Prop) (D : (ℕ → ℝ) → Prop)
    (J : Expr) (hi p : ℕ) : Prop :=
  ∃ (env : ℕ → ℝ) (S : Expr) (k : ℕ) (δ : ℝ), k ≤ p ∧ S.isPoly = true ∧
    S.eval (Function.update env hi 0) ≠ 0 ∧ 0 < δ ∧
    ∀ t : ℝ, 0 < t → t < δ → D (Function.update env hi t) ∧ OK (Function.update env hi t) ∧
      drift F J (Function.update env hi t) = t ^ k * S.eval (Function.update env hi t)

section
variable {F : (ℕ → ℝ) → (ℕ → ℝ)} {OK : (ℕ → ℝ) → Prop} {D : (ℕ → ℝ) → Prop} {J R : Expr}
  {hi p : ℕ}

/-- **Per-step drift bound.** On every set `S` on which `|R| ≤ M` (within `D`),
`|J(F z) − J(z)| ≤ M · |h|^(p+1)`. -/
theorem order_drift_le (hcert : OrderVerified F OK D J R hi p) {S : Set (ℕ → ℝ)} {M : ℝ}
    (hM : ∀ env ∈ S, D env → |R.eval env| ≤ M) :
    ∀ env ∈ S, D env → |drift F J env| ≤ M * |env hi| ^ (p + 1) := by
  intro env hS hD
  rw [(hcert.2 env hD).2.2, abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM env hS hD) (by positivity)

/-- **Per-step drift bound on compact sets.** If `R` is a polynomial, then on every compact
set `K` of environments there is an `M` with `|J(F z) − J(z)| ≤ M · |h|^(p+1)` on `K ∩ D`. -/
theorem order_drift_compact (hcert : OrderVerified F OK D J R hi p) (hR : R.isPoly = true)
    {K : Set (ℕ → ℝ)} (hK : IsCompact K) :
    ∃ M, ∀ env ∈ K, D env → |drift F J env| ≤ M * |env hi| ^ (p + 1) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (R.continuous_eval_of_isPoly hR).continuousOn
  exact ⟨M, order_drift_le hcert fun env h _ => by simpa [Real.norm_eq_abs] using hM env h⟩

/-- A `VERIFIED` order certificate is never vacuous. -/
theorem order_verified_nonempty (hcert : OrderVerified F OK D J R hi p) :
    ∃ env, D env ∧ OK env :=
  let ⟨env, h⟩ := hcert.1
  ⟨env, h, (hcert.2 env h).1⟩

/-- **Lower bound behind a `REFUTED` order certificate.** At the certificate's point, the drift
with `h := t` is at least `c · t^k` for every `t ∈ (0, δ)`, with `c > 0` and `k ≤ p`. -/
theorem order_refuted_lower (hcert : OrderRefuted F OK D J hi p) :
    ∃ env : ℕ → ℝ, ∃ k ≤ p, ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      D (Function.update env hi t) ∧ OK (Function.update env hi t) ∧
        c * t ^ k ≤ |drift F J (Function.update env hi t)| := by
  obtain ⟨env, S, k, δ, hk, hS, h0, hδ, hall⟩ := hcert
  have hc : 0 < |S.eval (Function.update env hi 0)| := abs_pos.mpr h0
  have hcont : Continuous fun t : ℝ => S.eval (Function.update env hi t) :=
    (S.continuous_eval_of_isPoly hS).comp (continuous_const.update hi continuous_id)
  obtain ⟨ε, hε, hball⟩ := Metric.continuous_iff.mp hcont 0 _ (half_pos hc)
  refine ⟨env, k, hk, _, half_pos hc, min δ ε, lt_min hδ hε, fun t ht htδ => ?_⟩
  obtain ⟨hD, hOK, hdr⟩ := hall t ht (htδ.trans_le (min_le_left _ _))
  refine ⟨hD, hOK, ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htδ.trans_le (min_le_right _ _)
  have h1 := hball t hd
  rw [Real.dist_eq] at h1
  have h2 := abs_sub_abs_le_abs_sub (S.eval (Function.update env hi 0))
    (S.eval (Function.update env hi t))
  rw [abs_sub_comm] at h2
  have h3 : |S.eval (Function.update env hi 0)| / 2 ≤ |S.eval (Function.update env hi t)| := by
    linarith
  rw [hdr, abs_mul, abs_pow, abs_of_pos ht]
  have := mul_le_mul_of_nonneg_left h3 (pow_pos ht k).le
  linarith

/-- **Meaning of a `REFUTED` order certificate.** There is a point `z` such that, with
`h := t`, `z` is in `D` and junk-free for all small `t > 0`, and the drift at `z` is not
`O(t^(p+1))` as `t → 0⁺`. -/
theorem order_refuted_meaning (hcert : OrderRefuted F OK D J hi p) :
    ∃ env : ℕ → ℝ,
      (∀ᶠ t in 𝓝[>] (0 : ℝ), D (Function.update env hi t) ∧ OK (Function.update env hi t)) ∧
      ¬ ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
          |drift F J (Function.update env hi t)| ≤ C * t ^ (p + 1) := by
  obtain ⟨env, k, hk, c, hc, δ, hδ, hall⟩ := order_refuted_lower hcert
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < δ :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht
  refine ⟨env, hev.mono fun t ht => ⟨(hall t ht.1 ht.2).1, (hall t ht.1 ht.2).2.1⟩, ?_⟩
  rintro ⟨C, hC⟩
  have hε : 0 < min 1 (c / (|C| + 1)) := lt_min one_pos (by positivity)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min 1 (c / (|C| + 1)) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hε) fun t ht => ht.2
  obtain ⟨t, ⟨ht0, htδ⟩, hb, hts⟩ := (hev.and (hC.and hsmall)).exists
  have ht1 : t ≤ 1 := (hts.trans_le (min_le_left _ _)).le
  have htc : t * (|C| + 1) < c :=
    (lt_div_iff₀ (by positivity)).mp (hts.trans_le (min_le_right _ _))
  have hlow := (hall t ht0 htδ).2.2
  set m := p + 1 - k with hm
  have hm0 : m ≠ 0 := by omega
  have hpow : t ^ (p + 1) = t ^ k * t ^ m := by rw [← pow_add]; congr 1; omega
  have htm : t ^ m ≤ t := pow_le_of_le_one ht0.le ht1 hm0
  have htk : 0 < t ^ k := pow_pos ht0 k
  have e1 : c * t ^ k ≤ (C * t ^ m) * t ^ k := by rw [hpow] at hb; linarith
  have e2 : c ≤ C * t ^ m := le_of_mul_le_mul_right e1 htk
  have e3 : C * t ^ m ≤ |C| * t :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg ht0.le m)).trans
      (mul_le_mul_of_nonneg_left htm (abs_nonneg C))
  nlinarith [abs_nonneg C]

end

/-! ### The two forms: explicit maps and straight-line kernels -/

/-- `VERIFIED` `update_conserves_order_p` for an explicit map. -/
def UpdateOrderVerified (Phi : List Expr) (D : (ℕ → ℝ) → Prop) (J R : Expr) (hi p : ℕ) : Prop :=
  OrderVerified (updateStep Phi) (UpdateOK Phi J) D J R hi p

/-- `REFUTED` `update_conserves_order_p` for an explicit map. -/
def UpdateOrderRefuted (Phi : List Expr) (D : (ℕ → ℝ) → Prop) (J : Expr) (hi p : ℕ) : Prop :=
  OrderRefuted (updateStep Phi) (UpdateOK Phi J) D J hi p

/-- `VERIFIED` `update_conserves_order_p` for a straight-line kernel. -/
def KernelOrderVerified (prog : Prog) (D : (ℕ → ℝ) → Prop) (J R : Expr) (hi p : ℕ) : Prop :=
  OrderVerified (exec prog) (KernelOK prog J) D J R hi p

/-- `REFUTED` `update_conserves_order_p` for a straight-line kernel. -/
def KernelOrderRefuted (prog : Prog) (D : (ℕ → ℝ) → Prop) (J : Expr) (hi p : ℕ) : Prop :=
  OrderRefuted (exec prog) (KernelOK prog J) D J hi p

/-- **Meaning of `VERIFIED` (`update_conserves_order_p`, explicit map), per step.** On every
set where `|R| ≤ M`, `|J(Φ(z)) − J(z)| ≤ M · |h|^(p+1)`. With `R` a polynomial, some `M`
works on every compact set (`order_drift_compact`). Nothing is claimed about orbits. -/
theorem update_order_meaning {Phi : List Expr} {D : (ℕ → ℝ) → Prop} {J R : Expr} {hi p : ℕ}
    (hcert : UpdateOrderVerified Phi D J R hi p) {S : Set (ℕ → ℝ)} {M : ℝ}
    (hM : ∀ env ∈ S, D env → |R.eval env| ≤ M) :
    ∀ env ∈ S, D env → |J.eval (updateStep Phi env) - J.eval env| ≤ M * |env hi| ^ (p + 1) :=
  order_drift_le hcert hM

/-- **Meaning of `REFUTED` (`update_conserves_order_p`, explicit map).** At some point `z`
(in `D` and junk-free for all small `h > 0`), `J(Φ(z)) − J(z)` is not `O(h^(p+1))` as
`h → 0⁺`. -/
theorem update_order_refuted_meaning {Phi : List Expr} {D : (ℕ → ℝ) → Prop} {J : Expr}
    {hi p : ℕ} (hcert : UpdateOrderRefuted Phi D J hi p) :
    ∃ env : ℕ → ℝ,
      (∀ᶠ t in 𝓝[>] (0 : ℝ), D (Function.update env hi t) ∧
        UpdateOK Phi J (Function.update env hi t)) ∧
      ¬ ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
          |J.eval (updateStep Phi (Function.update env hi t)) - J.eval (Function.update env hi t)|
            ≤ C * t ^ (p + 1) :=
  order_refuted_meaning hcert

/-- **Meaning of `VERIFIED` (`update_conserves_order_p`, kernel), per step.** As
`update_order_meaning`, with `exec prog` for `Φ`. -/
theorem kernel_order_meaning {prog : Prog} {D : (ℕ → ℝ) → Prop} {J R : Expr} {hi p : ℕ}
    (hcert : KernelOrderVerified prog D J R hi p) {S : Set (ℕ → ℝ)} {M : ℝ}
    (hM : ∀ env ∈ S, D env → |R.eval env| ≤ M) :
    ∀ env ∈ S, D env → |J.eval (exec prog env) - J.eval env| ≤ M * |env hi| ^ (p + 1) :=
  order_drift_le hcert hM

/-- **Meaning of `REFUTED` (`update_conserves_order_p`, kernel).** As
`update_order_refuted_meaning`, with `exec prog` for `Φ`. -/
theorem kernel_order_refuted_meaning {prog : Prog} {D : (ℕ → ℝ) → Prop} {J : Expr} {hi p : ℕ}
    (hcert : KernelOrderRefuted prog D J hi p) :
    ∃ env : ℕ → ℝ,
      (∀ᶠ t in 𝓝[>] (0 : ℝ), D (Function.update env hi t) ∧
        KernelOK prog J (Function.update env hi t)) ∧
      ¬ ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
          |J.eval (exec prog (Function.update env hi t)) - J.eval (Function.update env hi t)|
            ≤ C * t ^ (p + 1) :=
  order_refuted_meaning hcert

end PhysVerify
