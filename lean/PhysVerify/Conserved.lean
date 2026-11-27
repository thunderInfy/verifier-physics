import PhysVerify.EulerLagrange
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Conserved quantities of the Euler–Lagrange flow

A claim gives a Lagrangian `L`, a domain `D` and an expression `Q` in `(q, q̇, parameters)`,
and says: `Q` is constant along every solution of the Euler–Lagrange equations of `L` that
stays in `D`.

* **`VERIFIED`** (`ConservedVerified`) is Noether's characteristic form: on `D`,
  `dt n Q = Σ_k λ_k · EL n k L` as an identity in the jet `(q, q̇, q̈)`, for multipliers `λ_k`
  supplied by the untrusted planner. Along a solution every `EL_k` vanishes, so `dQ/dt = 0`
  (`conserved_deriv_zero`), and `Q` is constant on every open time interval on which the
  jet stays in `D` (`conserved_meaning`).
* **`REFUTED`** (`ConservedRefuted`) is a jet in `D` where the Euler–Lagrange system holds,
  the velocity Hessian of `L` is invertible, and `dt n Q ≠ 0`. `conserved_refuted_meaning`:
  every trajectory twice differentiable at `t` with that jet at `t` satisfies the real
  Euler–Lagrange equations at `t`, and along it `dQ/dt ≠ 0` at `t`. That some *solution* of
  the Euler–Lagrange equations passes through the jet is not proved here: it needs an
  existence theorem (Picard–Lindelöf for the regular system `q̈ = H⁻¹ (…)`), and is
  assumed.

The value of `λ_k` never matters for soundness: on a solution `Σ λ_k · 0 = 0` for any reals
`λ_k`. The certificate still requires `diffOK` and `physOK` of every `λ_k` on `D`, so a
certificate whose multipliers take junk values somewhere in `D` is rejected.
-/

namespace PhysVerify
open Expr Filter Topology Set

/-- `Σ_i λ_i · EL n (k + i) L` over the list `λs`, starting at index `k`. -/
noncomputable def lamSum (n : ℕ) (L : Expr) (env : ℕ → ℝ) : ℕ → List Expr → ℝ
  | _, [] => 0
  | k, l :: ls => l.eval env * (EL n k L).eval env + lamSum n L env (k + 1) ls

lemma lamSum_eq_zero (n : ℕ) (L : Expr) (env : ℕ → ℝ) :
    ∀ (ls : List Expr) (k : ℕ), (∀ i < ls.length, (EL n (k + i) L).eval env = 0) →
      lamSum n L env k ls = 0
  | [], _, _ => rfl
  | l :: ls, k, h => by
      have h0 := h 0 (by simp)
      have ih := lamSum_eq_zero n L env ls (k + 1) fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this
      simp only [lamSum, ih, add_zero]
      simp at h0
      rw [h0, mul_zero]

/-- The velocity Hessian `∂²L/∂q̇_i∂q̇_j` is invertible at `env`. -/
def Regular (n : ℕ) (L : Expr) (env : ℕ → ℝ) : Prop :=
  (Matrix.of fun i j : Fin n => ((L.deriv (n + i)).deriv (n + j)).eval env).det ≠ 0

/-- What a `VERIFIED` conserved-quantity certificate proves (the judge writes it with
concrete `n L D Q λs`, together with `NoAccel` of `L`, `Q` and every `λ_k`,
`λs.length = n` and `DomainForm`). -/
def ConservedVerified (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (Q : Expr)
    (lams : List Expr) : Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → DomainOK n L env ∧ L.physOK env ∧ Q.diffOK env ∧ Q.physOK env ∧
      (∀ l ∈ lams, l.diffOK env ∧ l.physOK env) ∧
      (dt n Q).eval env = lamSum n L env 0 lams

/-- What a `REFUTED` conserved-quantity certificate proves. -/
def ConservedRefuted (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (Q : Expr) : Prop :=
  ∃ env, D env ∧ DomainOK n L env ∧ L.physOK env ∧ Q.diffOK env ∧ Q.physOK env ∧
    ELSystem n L env ∧ Regular n L env ∧ (dt n Q).eval env ≠ 0

/-- Along a trajectory twice differentiable at `t`, every variable other than an
acceleration moves with the velocity `timeDir` prescribes. -/
lemma trajEnv_hasDerivAt {n : ℕ} {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (j : ℕ) (h : j < 2 * n ∨ 3 * n ≤ j) :
    HasDerivAt (fun s => trajEnv n q p s j) ((timeDir n j).eval (fun i => trajEnv n q p t i)) t := by
  rcases h with h | h
  · by_cases hjn : j < n
    · have : (fun s => trajEnv n q p s j) = q j := by funext s; simp [trajEnv, hjn]
      rw [this]
      have e : (timeDir n j).eval (fun i => trajEnv n q p t i) = _root_.deriv (q j) t := by
        simp only [timeDir, h, if_true, eval, trajEnv]
        rw [if_neg (by omega), if_pos (by omega)]
        congr 2; omega
      rw [e]; exact (hq1 j hjn).hasDerivAt
    · have : (fun s => trajEnv n q p s j) = _root_.deriv (q (j - n)) := by
        funext s; simp [trajEnv, hjn, h]
      rw [this]
      have e : (timeDir n j).eval (fun i => trajEnv n q p t i) =
          _root_.deriv (_root_.deriv (q (j - n))) t := by
        simp only [timeDir, h, if_true, eval, trajEnv]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        congr 3; omega
      rw [e]; exact (hq2 (j - n) (by omega)).hasDerivAt
  · have : (fun s => trajEnv n q p s j) = fun _ => p j := by
      funext s; simp only [trajEnv]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [this]
    have e : (timeDir n j).eval (fun i => trajEnv n q p t i) = 0 := by
      simp only [timeDir]; rw [if_neg (by omega)]; simp [eval]
    rw [e]; exact hasDerivAt_const t (p j)

/-- **Chain rule along a trajectory.** For `Q` without accelerations, `dt n Q` on the jet is
the derivative of `s ↦ Q(q(s), q'(s), p)` at `t`. -/
theorem dt_hasDerivAt {n : ℕ} {Q : Expr} (hQ : NoAccel n Q)
    {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hd : Q.diffOK (trajEnv n q p t)) :
    HasDerivAt (fun s => Q.eval (trajEnv n q p s)) ((dt n Q).eval (trajEnv n q p t)) t :=
  hasDerivAt_dir (timeDir n) (fun j s => trajEnv n q p s j) t Q
    (fun j hj => trajEnv_hasDerivAt hq1 hq2 j (hQ j hj)) hd

/-- **`dQ/dt = 0` at `t`** along every trajectory twice differentiable at `t`, whose jet
stays in `D` near `t`, and which satisfies the real Euler–Lagrange equations at `t`. -/
theorem conserved_deriv_zero {n : ℕ} {L Q : Expr} {D : (ℕ → ℝ) → Prop} {lams : List Expr}
    (hcert : ConservedVerified n L D Q lams) (hlen : lams.length = n)
    (hacc : NoAccel n L) (hQ : NoAccel n Q)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hD : ∀ᶠ s in 𝓝 t, D (trajEnv n q p s))
    (hEL : ∀ k < n, realEL n k L q p t = 0) :
    HasDerivAt (fun s => Q.eval (trajEnv n q p s)) 0 t := by
  have hL : ∀ᶠ s in 𝓝 t, L.diffOK (trajEnv n q p s) :=
    hD.mono fun s hs => (hcert.2 _ hs).1.1
  obtain ⟨⟨_, hP⟩, _, hQd, _, _, hid⟩ := hcert.2 _ hD.self_of_nhds
  have h := dt_hasDerivAt hQ hq1 hq2 hQd
  rwa [hid, lamSum_eq_zero n L _ lams 0 fun i hi => by
    rw [zero_add, ← EL_bridge (by omega) L hacc q p t hq1 hq2 hL (hP i (by omega))]
    exact hEL i (by omega)] at h

/-- `conserved_deriv_zero` with the jet in `D` at `t` only (`DomainForm`: `D` is open). -/
theorem conserved_deriv_zero_at {n : ℕ} {L Q : Expr} {D : (ℕ → ℝ) → Prop} {lams : List Expr}
    {as : List Atom} (hcert : ConservedVerified n L D Q lams) (hlen : lams.length = n)
    (hacc : NoAccel n L) (hQ : NoAccel n Q) (hform : DomainForm n D as)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hD : D (trajEnv n q p t))
    (hEL : ∀ k < n, realEL n k L q p t = 0) :
    HasDerivAt (fun s => Q.eval (trajEnv n q p s)) 0 t :=
  conserved_deriv_zero hcert hlen hacc hQ q p t hq1 hq2
    ((Domain.eventually hq1 hq2 as hform.2 ((hform.1 _).1 hD)).mono fun _ hs => (hform.1 _).2 hs)
    hEL

/-- **Meaning of `VERIFIED`.** Let `q` be twice differentiable on an open time interval
`(a, b)`, with its jet in `D` and the real Euler–Lagrange equations of `L` holding at every
time in `(a, b)`. Then `dQ/dt = 0` on `(a, b)`, and `Q` takes the same value at any two
times in `(a, b)`. -/
theorem conserved_meaning {n : ℕ} {L Q : Expr} {D : (ℕ → ℝ) → Prop} {lams : List Expr}
    {as : List Atom} (hcert : ConservedVerified n L D Q lams) (hlen : lams.length = n)
    (hacc : NoAccel n L) (hQ : NoAccel n Q) (hform : DomainForm n D as)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (a b : ℝ)
    (hq1 : ∀ t ∈ Ioo a b, ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ t ∈ Ioo a b, ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hD : ∀ t ∈ Ioo a b, D (trajEnv n q p t))
    (hEL : ∀ t ∈ Ioo a b, ∀ k < n, realEL n k L q p t = 0) :
    (∀ t ∈ Ioo a b, _root_.deriv (fun s => Q.eval (trajEnv n q p s)) t = 0) ∧
      ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, Q.eval (trajEnv n q p s) = Q.eval (trajEnv n q p t) := by
  have hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s => Q.eval (trajEnv n q p s)) 0 t := fun t ht =>
    conserved_deriv_zero_at hcert hlen hacc hQ hform q p t (hq1 t ht) (hq2 t ht) (hD t ht)
      (hEL t ht)
  refine ⟨fun t ht => (hd t ht).deriv, ?_⟩
  have hdiff : DifferentiableOn ℝ (fun s => Q.eval (trajEnv n q p s)) (Ioo a b) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  exact fun s hs t ht => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
    (fun t ht => (hd t ht).deriv) hs ht

/-- **Meaning of `REFUTED`.** At the certificate's jet `env` (in `D`, with an invertible
velocity Hessian), every trajectory `q` twice differentiable at `t` whose jet at `t` is
`env` satisfies the real Euler–Lagrange equations at `t`, and `s ↦ Q(q(s), q'(s))` has a
non-zero derivative at `t`. The quadratic `jetTraj n env` is one such trajectory (at
`t = 0`). Not proved: that a solution of the Euler–Lagrange equations on an interval passes
through `env` (Picard–Lindelöf for the regular system); that step is assumed. -/
theorem conserved_refuted_meaning {n : ℕ} {L Q : Expr} {D : (ℕ → ℝ) → Prop}
    (hcert : ConservedRefuted n L D Q) (hacc : NoAccel n L) (hQ : NoAccel n Q) :
    ∃ env, D env ∧ Regular n L env ∧ (dt n Q).eval env ≠ 0 ∧
      trajEnv n (jetTraj n env) env 0 = env ∧
      ∀ (q : ℕ → ℝ → ℝ) (t : ℝ), (∀ j < n, DifferentiableAt ℝ (q j) t) →
        (∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t) → trajEnv n q env t = env →
        (∀ k < n, realEL n k L q env t = 0) ∧
          HasDerivAt (fun s => Q.eval (trajEnv n q env s)) ((dt n Q).eval env) t := by
  obtain ⟨env, hD, ⟨hL0, hP⟩, _, hQd, _, hEL, hreg, hne⟩ := hcert
  refine ⟨env, hD, hreg, hne, trajEnv_jetTraj n env, fun q t hq1 hq2 htr => ?_⟩
  have hL : ∀ᶠ s in 𝓝 t, L.diffOK (trajEnv n q env s) :=
    (continuousAt_eval (fun j s => trajEnv n q env s j) t L
      (fun j hj => trajEnv_continuousAt hq1 hq2 j (hacc j hj))
      (by simpa [htr] using hL0)).2
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [EL_bridge hk L hacc q env t hq1 hq2 hL (by rw [htr]; exact hP k hk), htr]
    exact hEL k hk
  · have := dt_hasDerivAt hQ hq1 hq2 (p := env) (by rw [htr]; exact hQd)
    rwa [htr] at this

/-- The quadratic trajectory through the jet is twice differentiable everywhere, so
`conserved_refuted_meaning` applies to it at `t = 0`. -/
theorem jetTraj_twice_differentiable (n : ℕ) (env : ℕ → ℝ) (t : ℝ) :
    (∀ j < n, DifferentiableAt ℝ (jetTraj n env j) t) ∧
      ∀ j < n, DifferentiableAt ℝ (_root_.deriv (jetTraj n env j)) t :=
  ⟨fun j _ => (jetTraj_hasDerivAt n env j t).differentiableAt,
   fun j _ => by rw [jetTraj_deriv]; fun_prop⟩

end PhysVerify
