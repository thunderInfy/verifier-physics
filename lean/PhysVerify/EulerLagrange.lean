import PhysVerify.Deriv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
-- tactics the certificate proofs use
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Euler–Lagrange equations as statements about `Expr`

**Index layout** for `n` degrees of freedom (k < n):

| variable | index    |
|----------|----------|
| `q_k`     | `k`      |
| `qdot_k`  | `n + k`  |
| `qddot_k` | `2n + k` |
| parameters | `3n, 3n+1, …` |

A Lagrangian is an `Expr` in the `q`, `qdot` and parameter variables (`NoAccel`).

* `dt n g` is the total time derivative along a trajectory, by the chain rule:
  every `q_k` moves with velocity `qdot_k` and every `qdot_k` with velocity `qddot_k`
  (`Expr.dir (timeDir n)`, i.e. `Σ_k ∂g/∂q_k · qdot_k + ∂g/∂qdot_k · qddot_k`).
* `EL n k L := dt n (∂L/∂qdot_k) − ∂L/∂q_k`.

Main results:

* `EL_bridge`: along any trajectory `q` that is twice differentiable at `t`, `EL n k L`
  evaluated on the jet `(q(t), q'(t), q''(t))` equals the real Euler–Lagrange expression
  `d/dt (∂L/∂q̇_k) − ∂L/∂q_k` (Mathlib `deriv`s of the actual function `L`), provided
  `L.diffOK` holds near `t` and `(∂L/∂qdot_k).diffOK` holds at `t`.
* `verified_meaning`: a `VERIFIED` certificate (pointwise equivalence of the EL system and
  the claimed equations on a domain `D`) implies that every such trajectory staying in `D`
  satisfies the real EL equations at `t` iff it satisfies the claimed equations at `t`.
* `verified_nonempty`: the certificate also proves that `D` has a point, and that on `D`
  no division, negative power, `sqrt`, `log` or non-integer power takes a junk value
  (`PhysOK`), in `L` or in the claimed equations.
* `refuted_meaning`: a `REFUTED` certificate (a domain point where the two disagree) yields
  an explicit smooth (quadratic) trajectory on which, at `t = 0`, the real EL equations and
  the claimed equations disagree.
* `ELSystem_iff_of_cert`: the certificate form `EL = C · (lhs − rhs)` with `det C ≠ 0`.
-/

namespace PhysVerify
open Expr Filter Topology

/-- Velocities along a trajectory: `q_k ↦ qdot_k`, `qdot_k ↦ qddot_k`, everything else 0. -/
def timeDir (n : ℕ) : ℕ → Expr := fun j => if j < 2 * n then .var (j + n) else .lit 0

/-- Total time derivative along a trajectory. -/
def dt (n : ℕ) (g : Expr) : Expr := g.dir (timeDir n)

/-- The `k`-th Euler–Lagrange expression `d/dt (∂L/∂qdot_k) − ∂L/∂q_k`. -/
def EL (n k : ℕ) (L : Expr) : Expr := .sub (dt n (L.deriv (n + k))) (L.deriv k)

/-- The Lagrangian does not mention accelerations. -/
def NoAccel (n : ℕ) (L : Expr) : Prop := ∀ j ∈ L.vars, j < 2 * n ∨ 3 * n ≤ j

instance (n : ℕ) (L : Expr) : Decidable (NoAccel n L) := by unfold NoAccel; infer_instance

/-- The jet of a trajectory `q` at time `s`, with parameters `p`. -/
noncomputable def trajEnv (n : ℕ) (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (s : ℝ) : ℕ → ℝ := fun j =>
  if j < n then q j s
  else if j < 2 * n then _root_.deriv (q (j - n)) s
  else if j < 3 * n then _root_.deriv (_root_.deriv (q (j - 2 * n))) s
  else p j

/-- The real Euler–Lagrange expression along `q` at time `t`, using Mathlib derivatives of
the function `(q, q̇) ↦ L`. -/
noncomputable def realEL (n k : ℕ) (L : Expr) (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ) : ℝ :=
  _root_.deriv (fun s => _root_.deriv
      (fun x => L.eval (Function.update (trajEnv n q p s) (n + k) x)) (_root_.deriv (q k) s)) t
    - _root_.deriv (fun x => L.eval (Function.update (trajEnv n q p t) k x)) (q k t)

lemma timeDir_vars (n : ℕ) (P : ℕ → Prop) (hP : ∀ j, n ≤ j → j < 3 * n → P j) :
    ∀ i, ∀ j ∈ (timeDir n i).vars, P j := by
  intro i j hj
  unfold timeDir at hj
  split_ifs at hj with h
  · simp [vars] at hj; subst hj; exact hP _ (by omega) (by omega)
  · simp [vars] at hj

/-- **Bridge lemma** (n degrees of freedom). -/
theorem EL_bridge {n k : ℕ} (hk : k < n) (L : Expr) (hacc : NoAccel n L)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hL : ∀ᶠ s in 𝓝 t, L.diffOK (trajEnv n q p s))
    (hP : (L.deriv (n + k)).diffOK (trajEnv n q p t)) :
    realEL n k L q p t = (EL n k L).eval (trajEnv n q p t) := by
  set P := L.deriv (n + k)
  have hPacc : ∀ j ∈ P.vars, j < 2 * n ∨ 3 * n ≤ j := vars_deriv _ L _ hacc
  -- every variable of P moves with the velocity `timeDir` prescribes
  have hγ : ∀ j ∈ P.vars, HasDerivAt (fun s => trajEnv n q p s j)
      ((timeDir n j).eval (fun i => trajEnv n q p t i)) t := by
    intro j hj
    rcases hPacc j hj with h | h
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
  have hdP := hasDerivAt_dir (timeDir n) (fun j s => trajEnv n q p s j) t P hγ hP
  -- the real partial derivative in qdot_k agrees with `P` near t
  have hslot : ∀ s, trajEnv n q p s (n + k) = _root_.deriv (q k) s := by
    intro s; simp only [trajEnv]; rw [if_neg (by omega), if_pos (by omega)]; congr 2; omega
  have hEq : (fun s => _root_.deriv
      (fun x => L.eval (Function.update (trajEnv n q p s) (n + k) x)) (_root_.deriv (q k) s))
      =ᶠ[𝓝 t] fun s => P.eval (trajEnv n q p s) := by
    filter_upwards [hL] with s hs
    have := hasDerivAt_deriv (n + k) L (trajEnv n q p s) hs
    rw [hslot] at this
    exact this.deriv
  have hq : trajEnv n q p t k = q k t := by simp [trajEnv, hk]
  have hLt : L.diffOK (trajEnv n q p t) := hL.self_of_nhds
  have h2 := (hasDerivAt_deriv k L (trajEnv n q p t) hLt)
  rw [hq] at h2
  unfold realEL
  rw [hEq.deriv_eq, h2.deriv, hdP.deriv]
  simp [EL, dt, eval, P]

/-! ### Certificates -/

/-- The Euler–Lagrange system holds at a jet. -/
def ELSystem (n : ℕ) (L : Expr) (env : ℕ → ℝ) : Prop := ∀ k < n, (EL n k L).eval env = 0

/-- The claimed equations hold at a jet. -/
def Claims (cs : List Law) (env : ℕ → ℝ) : Prop := ∀ c ∈ cs, c.Holds env

/-- Where the bridge lemma applies. -/
def DomainOK (n : ℕ) (L : Expr) (env : ℕ → ℝ) : Prop :=
  L.diffOK env ∧ ∀ k < n, (L.deriv (n + k)).diffOK env

/-- The literal `0`. -/
def Expr.isZero : Expr → Bool
  | .lit q => q == 0
  | _ => false

/-- Both sides of an equation have the same dimension; a literal `0` on either side has
every dimension. -/
def Law.dimOK (ctx : List Dim) (c : Law) : Bool :=
  match c.lhs.dimOf ctx, c.rhs.dimOf ctx with
  | some x, some y => decide (x = y) || c.lhs.isZero || c.rhs.isZero
  | _, _ => false

/-- The Lagrangian is well-dimensioned and every claimed equation is dimensionally
consistent (checked by `decide` in every `VERIFIED` certificate). -/
def dimsOK (ctx : List Dim) (L : Expr) (cs : List Law) : Bool :=
  (L.dimOf ctx).isSome && cs.all (Law.dimOK ctx)

/-- No junk values (`Expr.physOK`) in the Lagrangian or in either side of a claimed
equation. -/
def PhysOK (L : Expr) (cs : List Law) (env : ℕ → ℝ) : Prop :=
  L.physOK env ∧ ∀ c ∈ cs, c.lhs.physOK env ∧ c.rhs.physOK env

/-- What a `VERIFIED` certificate proves (the judge writes this with concrete `n L D cs`).
The first conjunct rules out a vacuous certificate on an empty domain. -/
def Verified (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → DomainOK n L env ∧ PhysOK L cs env ∧ (ELSystem n L env ↔ Claims cs env)

/-- What a `REFUTED` certificate proves. -/
def Refuted (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  ∃ env, D env ∧ DomainOK n L env ∧ PhysOK L cs env ∧ ¬(ELSystem n L env ↔ Claims cs env)

/-- A `VERIFIED` certificate is never vacuous: its domain has a point, where the
Lagrangian and the claimed equations take no junk values. -/
theorem verified_nonempty {n : ℕ} {L : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : Verified n L D cs) : ∃ env, D env ∧ PhysOK L cs env :=
  let ⟨env, h⟩ := hcert.1
  ⟨env, h, (hcert.2 env h).2.1⟩

theorem verified_meaning {n : ℕ} {L : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : Verified n L D cs) (hacc : NoAccel n L)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hD : ∀ᶠ s in 𝓝 t, D (trajEnv n q p s)) :
    (∀ k < n, realEL n k L q p t = 0) ↔ Claims cs (trajEnv n q p t) := by
  have hL : ∀ᶠ s in 𝓝 t, L.diffOK (trajEnv n q p s) :=
    hD.mono fun s hs => (hcert.2 _ hs).1.1
  obtain ⟨⟨_, hP⟩, _, hiff⟩ := hcert.2 _ hD.self_of_nhds
  rw [← hiff]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  rw [EL_bridge hk L hacc q p t hq1 hq2 hL (hP k hk)]

/-! ### Open domains

The parser admits only domains that are conjunctions of atoms `a < b` and `a ≠ b`, with
`a`, `b` in the fragment `Expr.contOK` and no accelerations. The judge writes `D` as that
conjunction and proves `DomainForm n D as` for the atoms `as` (by `Iff.rfl` and `decide`).
Such a `D` is open, and along a trajectory twice differentiable at `t`, a jet in `D` at
`t` stays in `D` near `t`. So `verified_meaning_at` needs `D` only at `t`. -/

/-- A domain atom: `a < b` or `a ≠ b`. -/
inductive Atom
  | lt (a b : Expr)
  | ne (a b : Expr)

def Atom.Holds (env : ℕ → ℝ) : Atom → Prop
  | .lt a b => a.eval env < b.eval env
  | .ne a b => a.eval env ≠ b.eval env

/-- Both sides in the continuous fragment, and no accelerations. -/
def Atom.ok (n : ℕ) : Atom → Bool
  | .lt a b | .ne a b => a.contOK && b.contOK &&
      (a.vars ++ b.vars).all fun j => decide (j < 2 * n) || decide (3 * n ≤ j)

/-- The conjunction of the atoms, nested as the judge writes it (`True` if there are none). -/
def Domain (env : ℕ → ℝ) : List Atom → Prop
  | [] => True
  | [x] => x.Holds env
  | x :: y :: xs => x.Holds env ∧ Domain env (y :: xs)

/-- `D` is the conjunction of the atoms `as`, all in the fragment. -/
def DomainForm (n : ℕ) (D : (ℕ → ℝ) → Prop) (as : List Atom) : Prop :=
  (∀ env, D env ↔ Domain env as) ∧ as.all (Atom.ok n) = true

lemma Atom.isOpen (n : ℕ) (x : Atom) (h : x.ok n = true) : IsOpen {env | x.Holds env} := by
  cases x with
  | lt a b =>
      simp only [ok, Bool.and_eq_true] at h
      exact isOpen_lt (Expr.continuous_eval_of_contOK a h.1.1)
        (Expr.continuous_eval_of_contOK b h.1.2)
  | ne a b =>
      simp only [ok, Bool.and_eq_true] at h
      exact isOpen_ne_fun (Expr.continuous_eval_of_contOK a h.1.1)
        (Expr.continuous_eval_of_contOK b h.1.2)

lemma Domain.isOpen (n : ℕ) : ∀ as : List Atom, as.all (Atom.ok n) = true →
    IsOpen {env | Domain env as}
  | [], _ => by simp [Domain]
  | [x], h => by simpa [Domain] using x.isOpen n (by simpa using h)
  | x :: y :: xs, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact (x.isOpen n h.1).inter (Domain.isOpen n (y :: xs) (by simpa using h.2))

/-- **Openness.** A domain the parser admits is an open set of environments (product
topology: each atom depends on finitely many coordinates). -/
theorem DomainForm.isOpen {n : ℕ} {D : (ℕ → ℝ) → Prop} {as : List Atom}
    (h : DomainForm n D as) : IsOpen {env | D env} := by
  have : {env | D env} = {env | Domain env as} := Set.ext fun env => h.1 env
  rw [this]; exact Domain.isOpen n as h.2

/-- Along a trajectory twice differentiable at `t`, the jet's positions, velocities and
parameters are continuous at `t` (the accelerations need not be). -/
lemma trajEnv_continuousAt {n : ℕ} {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (j : ℕ) (hj : j < 2 * n ∨ 3 * n ≤ j) :
    ContinuousAt (fun s => trajEnv n q p s j) t := by
  rcases hj with h | h
  · by_cases hjn : j < n
    · have : (fun s => trajEnv n q p s j) = q j := by funext s; simp [trajEnv, hjn]
      rw [this]; exact (hq1 j hjn).continuousAt
    · have : (fun s => trajEnv n q p s j) = _root_.deriv (q (j - n)) := by
        funext s; simp [trajEnv, hjn, h]
      rw [this]; exact (hq2 (j - n) (by omega)).continuousAt
  · have : (fun s => trajEnv n q p s j) = fun _ => p j := by
      funext s; simp only [trajEnv]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [this]; exact continuousAt_const

lemma Expr.continuousAt_trajEnv {n : ℕ} {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (e : Expr) (he : e.contOK = true) (hv : ∀ j ∈ e.vars, j < 2 * n ∨ 3 * n ≤ j) :
    ContinuousAt (fun s => e.eval (trajEnv n q p s)) t :=
  (Expr.continuousAt_eval (fun j s => trajEnv n q p s j) t e
    (fun j hj => trajEnv_continuousAt hq1 hq2 j (hv j hj))
    (Expr.diffOK_of_contOK _ e he)).1

lemma Atom.eventually {n : ℕ} {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (x : Atom) (hx : x.ok n = true) (h : x.Holds (trajEnv n q p t)) :
    ∀ᶠ s in 𝓝 t, x.Holds (trajEnv n q p s) := by
  cases x with
  | lt a b =>
      simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_append, Bool.or_eq_true,
        decide_eq_true_eq] at hx
      exact (Expr.continuousAt_trajEnv hq1 hq2 a hx.1.1 fun j hj => hx.2 j (.inl hj)).eventually_lt
        (Expr.continuousAt_trajEnv hq1 hq2 b hx.1.2 fun j hj => hx.2 j (.inr hj)) h
  | ne a b =>
      simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_append, Bool.or_eq_true,
        decide_eq_true_eq] at hx
      have hc := (Expr.continuousAt_trajEnv (p := p) hq1 hq2 a hx.1.1
          fun j hj => hx.2 j (.inl hj)).sub
        (Expr.continuousAt_trajEnv (p := p) hq1 hq2 b hx.1.2 fun j hj => hx.2 j (.inr hj))
      exact (hc.eventually_ne (sub_ne_zero.2 h)).mono fun _ hs => sub_ne_zero.1 hs

lemma Domain.eventually {n : ℕ} {q : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {t : ℝ}
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t) :
    ∀ as : List Atom, as.all (Atom.ok n) = true → Domain (trajEnv n q p t) as →
      ∀ᶠ s in 𝓝 t, Domain (trajEnv n q p s) as
  | [], _, _ => by simp [Domain]
  | [x], hx, h => x.eventually hq1 hq2 (by simpa using hx) h
  | x :: y :: xs, hx, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hx
      exact (x.eventually hq1 hq2 hx.1 h.1).and
        (Domain.eventually hq1 hq2 (y :: xs) (by simpa using hx.2) h.2)

/-- **`verified_meaning` with the domain at `t` only.** For a domain of the form the parser
admits (`DomainForm`, proven in every `VERIFIED` certificate), every trajectory twice
differentiable at `t` whose jet is in `D` at `t` satisfies the real Euler–Lagrange
equations at `t` iff it satisfies the claimed equations at `t`. -/
theorem verified_meaning_at {n : ℕ} {L : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    {as : List Atom} (hcert : Verified n L D cs) (hacc : NoAccel n L) (hform : DomainForm n D as)
    (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hq1 : ∀ j < n, DifferentiableAt ℝ (q j) t)
    (hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (q j)) t)
    (hD : D (trajEnv n q p t)) :
    (∀ k < n, realEL n k L q p t = 0) ↔ Claims cs (trajEnv n q p t) :=
  verified_meaning hcert hacc q p t hq1 hq2
    ((Domain.eventually hq1 hq2 as hform.2 ((hform.1 _).1 hD)).mono fun _ hs => (hform.1 _).2 hs)

/-- The quadratic trajectory through a jet. -/
noncomputable def jetTraj (n : ℕ) (env : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  fun j s => env j + env (n + j) * s + env (2 * n + j) * s ^ 2 / 2

lemma jetTraj_hasDerivAt (n : ℕ) (env : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    HasDerivAt (jetTraj n env j) (env (n + j) + env (2 * n + j) * s) s := by
  have h : HasDerivAt (fun x => env j + env (n + j) * x + env (2 * n + j) * x ^ 2 / 2)
      (env (n + j) * 1 + env (2 * n + j) * ((2 : ℕ) * s ^ (2 - 1)) / 2) s :=
    (((hasDerivAt_id' s).const_mul (env (n + j))).const_add (env j)).add
      (((hasDerivAt_pow 2 s).const_mul (env (2 * n + j))).div_const 2)
  have e : env (n + j) * 1 + env (2 * n + j) * ((2 : ℕ) * s ^ (2 - 1)) / 2 =
      env (n + j) + env (2 * n + j) * s := by push_cast; ring
  rw [e] at h
  exact h

lemma jetTraj_deriv (n : ℕ) (env : ℕ → ℝ) (j : ℕ) :
    _root_.deriv (jetTraj n env j) = fun s => env (n + j) + env (2 * n + j) * s :=
  funext fun s => (jetTraj_hasDerivAt n env j s).deriv

lemma deriv_jetVel (a b : ℝ) : _root_.deriv (fun s : ℝ => a + b * s) = fun _ => b := by
  funext s
  have := ((hasDerivAt_id' s).const_mul b).const_add a
  simpa using this.deriv

lemma trajEnv_jetTraj (n : ℕ) (env : ℕ → ℝ) : trajEnv n (jetTraj n env) env 0 = env := by
  funext j
  simp only [trajEnv, jetTraj_deriv, deriv_jetVel]
  split_ifs with h1 h2 h3
  · simp [jetTraj]
  · simp only [mul_zero, add_zero]; congr 1; omega
  · congr 1; omega
  · rfl

lemma trajEnv_jetTraj_continuous (n : ℕ) (env : ℕ → ℝ) (j : ℕ) :
    Continuous (fun s => trajEnv n (jetTraj n env) env s j) := by
  simp only [trajEnv, jetTraj_deriv, deriv_jetVel]
  split_ifs
  · exact continuous_iff_continuousAt.2 fun s => (jetTraj_hasDerivAt n env j s).continuousAt
  · fun_prop
  · fun_prop
  · fun_prop

theorem refuted_meaning {n : ℕ} {L : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : Refuted n L D cs) (hacc : NoAccel n L) :
    ∃ env, D env ∧
      ¬((∀ k < n, realEL n k L (jetTraj n env) env 0 = 0) ↔
        Claims cs (trajEnv n (jetTraj n env) env 0)) := by
  obtain ⟨env, hD, ⟨hL0, hP⟩, _, hne⟩ := hcert
  refine ⟨env, hD, ?_⟩
  have hL : ∀ᶠ s in 𝓝 (0 : ℝ), L.diffOK (trajEnv n (jetTraj n env) env s) :=
    (continuousAt_eval (fun j s => trajEnv n (jetTraj n env) env s j) 0 L
      (fun j _ => (trajEnv_jetTraj_continuous n env j).continuousAt)
      (by simpa [trajEnv_jetTraj] using hL0)).2
  have hq1 : ∀ j < n, DifferentiableAt ℝ (jetTraj n env j) 0 :=
    fun j _ => (jetTraj_hasDerivAt n env j 0).differentiableAt
  have hq2 : ∀ j < n, DifferentiableAt ℝ (_root_.deriv (jetTraj n env j)) 0 := by
    intro j _; rw [jetTraj_deriv]; fun_prop
  rw [trajEnv_jetTraj]
  intro h
  apply hne
  rw [← h]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  have := EL_bridge hk L hacc (jetTraj n env) env 0 hq1 hq2 hL
    (by rw [trajEnv_jetTraj]; exact hP k hk)
  rw [this, trajEnv_jetTraj]

/-- Certificate form: `EL_k = Σ_j C k j · (lhs_j − rhs_j)` with `det C ≠ 0`. -/
theorem ELSystem_iff_of_cert {n : ℕ} {L : Expr} {cs : List Law} {env : ℕ → ℝ}
    (hlen : cs.length = n) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (h : ∀ k : Fin n, (EL n k L).eval env =
      ∑ j : Fin n, C k j * ((cs.get (j.cast hlen.symm)).lhs.eval env -
        (cs.get (j.cast hlen.symm)).rhs.eval env)) :
    ELSystem n L env ↔ Claims cs env := by
  set y : Fin n → ℝ := fun j => (cs.get (j.cast hlen.symm)).lhs.eval env -
    (cs.get (j.cast hlen.symm)).rhs.eval env
  have hEL : ∀ k : Fin n, (EL n k L).eval env = (C.mulVec y) k := by
    intro k; rw [h k]; rfl
  have hclaims : Claims cs env ↔ y = 0 := by
    constructor
    · intro hc; funext j
      have := hc (cs.get (j.cast hlen.symm)) (List.get_mem cs (j.cast hlen.symm))
      show _ - _ = (0 : ℝ)
      exact sub_eq_zero.mpr this
    · intro hy c hc
      obtain ⟨i, rfl⟩ := List.get_of_mem hc
      have := congrFun hy (i.cast hlen)
      simp only [y, Pi.zero_apply, sub_eq_zero] at this
      simpa [Law.Holds] using this
  rw [hclaims]
  constructor
  · intro hs
    apply Matrix.eq_zero_of_mulVec_eq_zero hC
    funext k; rw [← hEL]; exact hs k k.isLt
  · intro hy k hk
    have := hEL ⟨k, hk⟩
    simp only [hy, Matrix.mulVec_zero, Pi.zero_apply] at this
    exact this

end PhysVerify
