import PhysVerify.EulerLagrange

/-!
# Discrete mechanics: variational integrators

A discrete Lagrangian `L_d(q0, q1; h)` approximates the action of one time step. It is an
`Expr` in the same variable layout as a continuous Lagrangian, with the time levels in place
of the jet (n degrees of freedom, k < n):

| variable | index    |
|----------|----------|
| `q0_k`    | `k`      |
| `q1_k`    | `n + k`  |
| `q2_k`    | `2n + k` |
| `h`, parameters | `3n, 3n+1, …` |

`L_d` mentions only `q0`, `q1` and the parameters: that is `NoAccel n L_d` (no variable in
`[2n, 3n)`), the same predicate the continuous layer uses for "no accelerations".

* `shift n` relabels one step forward in time (`q0 ↦ q1`, `q1 ↦ q2`, parameters fixed), so
  `(e.ren (shift n))` is `e(q1, q2)` when `e` is `e(q0, q1)`.
* `DEL n k L_d := D_{2,k} L_d(q0, q1) + D_{1,k} L_d(q1, q2)`, the discrete Euler–Lagrange
  expression.

Main results:

* `DEL_bridge`: along a discrete trajectory `q : ℕ → ℕ → ℝ` (time level, coordinate), `DEL`
  at step `k` equals the real derivatives of the function `L_d` (`realDEL`).
* `del_verified_meaning` / `del_refuted_meaning`: the claimed update is (is not) equivalent to
  the real DEL equations.
* `dmomentum_meaning` (**discrete Noether, certificate form**): if on `D`
  `J(q1, q2) − J(q0, q1) = Σ_k μ_k · DEL_k` (multipliers from an untrusted search), then along
  every discrete trajectory whose triples stay in `D` and satisfy the real DEL equations,
  `J(q_N, q_{N+1}) = J(q_0, q_1)` exactly, for every `N`.
* `dmomentum_refuted_meaning`: a three-point discrete trajectory (it satisfies the real DEL
  equations) on which `J` changes; `RegularStep` (the matrix `∂DEL/∂q2` is invertible) says
  `q2` is the step the integrator takes from `(q0, q1)`. That `q2` is then locally unique is
  the implicit function theorem; it is not formalised here.

Lean totalises `x/0`, `sqrt` and `log` of negatives and `rpow`. Every certificate requires
`diffOK` of `L_d` at both points it is evaluated at (`StepOK`) and `physOK` (no junk values)
of `L_d`, the claimed residuals, `J` and the multipliers on `D`.
-/

namespace PhysVerify
open Expr

namespace Expr

/-- Relabel the variables of an expression. -/
def ren (f : ℕ → ℕ) : Expr → Expr
  | .var i => .var (f i)
  | .lit q => .lit q
  | .pi => .pi
  | .neg a => .neg (a.ren f)
  | .add a b => .add (a.ren f) (b.ren f)
  | .sub a b => .sub (a.ren f) (b.ren f)
  | .mul a b => .mul (a.ren f) (b.ren f)
  | .div a b => .div (a.ren f) (b.ren f)
  | .powi a n => .powi (a.ren f) n
  | .sqrt a => .sqrt (a.ren f)
  | .rpow a q => .rpow (a.ren f) q
  | .app g a => .app g (a.ren f)

theorem eval_ren (f : ℕ → ℕ) (env : ℕ → ℝ) (e : Expr) :
    (e.ren f).eval env = e.eval (fun i => env (f i)) := by
  induction e <;> simp_all [ren, eval]

theorem diffOK_ren (f : ℕ → ℕ) (env : ℕ → ℝ) (e : Expr) :
    (e.ren f).diffOK env ↔ e.diffOK (fun i => env (f i)) := by
  induction e with
  | app g a ih => cases g <;> simp_all [ren, diffOK, eval_ren]
  | _ => simp_all [ren, diffOK, eval_ren]

theorem physOK_ren (f : ℕ → ℕ) (env : ℕ → ℝ) (e : Expr) :
    (e.ren f).physOK env ↔ e.physOK (fun i => env (f i)) := by
  induction e with
  | app g a ih => cases g <;> simp_all [ren, physOK, eval_ren]
  | _ => simp_all [ren, physOK, eval_ren]

/-- The value of an expression depends only on the variables it mentions. -/
theorem eval_congr {env env' : ℕ → ℝ} :
    ∀ e : Expr, (∀ j ∈ e.vars, env j = env' j) → e.eval env = e.eval env'
  | .var i, h => by simpa [eval] using h i (by simp [vars])
  | .lit _, _ | .pi, _ => rfl
  | .neg a, h => by simp only [eval, eval_congr a h]
  | .powi a n, h => by simp only [eval, eval_congr a h]
  | .sqrt a, h => by simp only [eval, eval_congr a h]
  | .rpow a q, h => by simp only [eval, eval_congr a h]
  | .app g a, h => by simp only [eval, eval_congr a h]
  | .add a b, h | .sub a b, h | .mul a b, h | .div a b, h => by
      simp only [vars, List.mem_append] at h
      simp only [eval, eval_congr a fun j hj => h j (.inl hj), eval_congr b fun j hj => h j (.inr hj)]

end Expr

/-- One step forward in time: `q0_k ↦ q1_k`, `q1_k ↦ q2_k`; `h` and parameters fixed. -/
def shift (n j : ℕ) : ℕ := if j < 2 * n then j + n else j

/-- The `k`-th discrete Euler–Lagrange expression `D_{2,k} L_d(q0, q1) + D_{1,k} L_d(q1, q2)`. -/
def DEL (n k : ℕ) (Ld : Expr) : Expr := .add (Ld.deriv (n + k)) ((Ld.deriv k).ren (shift n))

/-- The discrete Euler–Lagrange system holds at `(q0, q1, q2)`. -/
def DELSystem (n : ℕ) (Ld : Expr) (env : ℕ → ℝ) : Prop := ∀ k < n, (DEL n k Ld).eval env = 0

/-- Where `DEL` is the real derivative: `L_d` is differentiable (`diffOK`) at `(q0, q1)` and
at `(q1, q2)`. The discrete counterpart of `DomainOK`, which asks for second derivatives. -/
def StepOK (n : ℕ) (Ld : Expr) (env : ℕ → ℝ) : Prop :=
  Ld.diffOK env ∧ (Ld.ren (shift n)).diffOK env

/-- Time levels `k, k + 1, k + 2` of a discrete trajectory `q` (time level, coordinate), and
the parameters `p`. -/
def stepEnv (n : ℕ) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k : ℕ) : ℕ → ℝ := fun j =>
  if j < n then q k j
  else if j < 2 * n then q (k + 1) (j - n)
  else if j < 3 * n then q (k + 2) (j - 2 * n)
  else p j

/-- The real discrete Euler–Lagrange expression at step `k`: Mathlib derivatives of the
function `L_d`, in its second argument at `(q_k, q_{k+1})` plus in its first argument at
`(q_{k+1}, q_{k+2})`. -/
noncomputable def realDEL (n i : ℕ) (Ld : Expr) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  _root_.deriv (fun x => Ld.eval (Function.update (stepEnv n q p k) (n + i) x)) (q (k + 1) i) +
    _root_.deriv (fun x => Ld.eval (Function.update (stepEnv n q p (k + 1)) i x)) (q (k + 1) i)

lemma stepEnv_shift (n : ℕ) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k j : ℕ) (hj : j < 2 * n ∨ 3 * n ≤ j) :
    stepEnv n q p k (shift n j) = stepEnv n q p (k + 1) j := by
  unfold stepEnv shift
  by_cases h1 : j < n
  · have a : j < 2 * n := by omega
    have b : ¬ j + n < n := by omega
    have c : j + n < 2 * n := by omega
    simp only [a, b, c, h1, ↓reduceIte]
    rw [show j + n - n = j by omega]
  · by_cases h2 : j < 2 * n
    · have b : ¬ j + n < n := by omega
      have c : ¬ j + n < 2 * n := by omega
      have d : j + n < 3 * n := by omega
      simp only [h1, h2, b, c, d, ↓reduceIte]
      rw [show j + n - 2 * n = j - n by omega]
    · have d : ¬ j < 3 * n := by omega
      simp only [h1, h2, d, ↓reduceIte]

/-- For `e(q0, q1)` (no `q2`), `e.ren (shift n)` at step `k` is `e` at step `k + 1`. -/
theorem eval_ren_shift {n : ℕ} {e : Expr} (he : NoAccel n e) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ)
    (k : ℕ) : (e.ren (shift n)).eval (stepEnv n q p k) = e.eval (stepEnv n q p (k + 1)) := by
  rw [eval_ren]
  exact eval_congr e fun j hj => stepEnv_shift n q p k j (he j hj)

/-- **Bridge lemma.** Where `L_d` is differentiable at both points, `DEL` evaluated at step
`k` is the real discrete Euler–Lagrange expression. -/
theorem DEL_bridge {n i : ℕ} (hi : i < n) {Ld : Expr} (hacc : NoAccel n Ld)
    (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k : ℕ) (hok : StepOK n Ld (stepEnv n q p k)) :
    realDEL n i Ld q p k = (DEL n i Ld).eval (stepEnv n q p k) := by
  set E : ℕ → ℝ := fun j => stepEnv n q p k (shift n j)
  have h0 := hasDerivAt_deriv (n + i) Ld _ hok.1
  have h1 := hasDerivAt_deriv i Ld E ((diffOK_ren _ _ _).1 hok.2)
  have e0 : stepEnv n q p k (n + i) = q (k + 1) i := by
    have a : ¬ n + i < n := by omega
    have b : n + i < 2 * n := by omega
    simp only [stepEnv, a, b, ↓reduceIte]
    rw [show n + i - n = i by omega]
  have e1 : E i = q (k + 1) i := by
    have a : i < 2 * n := by omega
    have b : ¬ i + n < n := by omega
    have c : i + n < 2 * n := by omega
    simp only [E, stepEnv, shift, a, b, c, ↓reduceIte]
    rw [show i + n - n = i by omega]
  have hfun : (fun x => Ld.eval (Function.update (stepEnv n q p (k + 1)) i x)) =
      fun x => Ld.eval (Function.update E i x) := by
    funext x
    refine eval_congr Ld fun j hj => ?_
    by_cases hji : j = i
    · subst hji; simp
    · simp only [Function.update_of_ne hji, E]
      exact (stepEnv_shift n q p k j (hacc j hj)).symm
  rw [e0] at h0
  rw [e1] at h1
  unfold realDEL
  rw [hfun, h0.deriv, h1.deriv]
  simp only [DEL, eval, eval_ren, E]

/-! ### `del_equations`: the claimed update is the DEL of `L_d` -/

/-- What a `VERIFIED` `del_equations` certificate proves. -/
def DELVerified (n : ℕ) (Ld : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → StepOK n Ld env ∧ PhysOK Ld cs env ∧ (Ld.ren (shift n)).physOK env ∧
      (DELSystem n Ld env ↔ Claims cs env)

/-- What a `REFUTED` `del_equations` certificate proves. -/
def DELRefuted (n : ℕ) (Ld : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  ∃ env, D env ∧ StepOK n Ld env ∧ PhysOK Ld cs env ∧ (Ld.ren (shift n)).physOK env ∧
    ¬(DELSystem n Ld env ↔ Claims cs env)

/-- Certificate form: `F_k = Σ_j C k j · (lhs_j − rhs_j)` with `det C ≠ 0` (as
`ELSystem_iff_of_cert`, for any family `F`). -/
theorem system_iff_of_cert {n : ℕ} {cs : List Law} {env : ℕ → ℝ} (F : ℕ → ℝ)
    (hlen : cs.length = n) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (h : ∀ k : Fin n, F k =
      ∑ j : Fin n, C k j * ((cs.get (j.cast hlen.symm)).lhs.eval env -
        (cs.get (j.cast hlen.symm)).rhs.eval env)) :
    (∀ k < n, F k = 0) ↔ Claims cs env := by
  set y : Fin n → ℝ := fun j => (cs.get (j.cast hlen.symm)).lhs.eval env -
    (cs.get (j.cast hlen.symm)).rhs.eval env
  have hF : ∀ k : Fin n, F k = (C.mulVec y) k := by
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
    funext k; rw [← hF]; exact hs k k.isLt
  · intro hy k hk
    have := hF ⟨k, hk⟩
    simp only [hy, Matrix.mulVec_zero, Pi.zero_apply] at this
    exact this

theorem DELSystem_iff_of_cert {n : ℕ} {Ld : Expr} {cs : List Law} {env : ℕ → ℝ}
    (hlen : cs.length = n) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (h : ∀ k : Fin n, (DEL n k Ld).eval env =
      ∑ j : Fin n, C k j * ((cs.get (j.cast hlen.symm)).lhs.eval env -
        (cs.get (j.cast hlen.symm)).rhs.eval env)) :
    DELSystem n Ld env ↔ Claims cs env :=
  system_iff_of_cert (fun k => (DEL n k Ld).eval env) hlen C hC h

/-- **Meaning of `VERIFIED` (`del_equations`).** At every step `k` of every discrete
trajectory whose triple `(q_k, q_{k+1}, q_{k+2})` is in `D`, the real DEL equations hold iff
the claimed update holds. -/
theorem del_verified_meaning {n : ℕ} {Ld : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : DELVerified n Ld D cs) (hacc : NoAccel n Ld) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k : ℕ)
    (hD : D (stepEnv n q p k)) :
    (∀ i < n, realDEL n i Ld q p k = 0) ↔ Claims cs (stepEnv n q p k) := by
  obtain ⟨hok, _, _, hiff⟩ := hcert.2 _ hD
  rw [← hiff]
  exact forall_congr' fun i => forall_congr' fun hi => by rw [DEL_bridge hi hacc q p k hok]

/-- A `VERIFIED` certificate is never vacuous. -/
theorem del_verified_nonempty {n : ℕ} {Ld : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : DELVerified n Ld D cs) : ∃ env, D env ∧ PhysOK Ld cs env :=
  let ⟨env, h⟩ := hcert.1
  ⟨env, h, (hcert.2 env h).2.1⟩

/-- The three-level trajectory stored in `env`: `q_k = env (k n + ·)` for `k = 0, 1, 2`. -/
def envTraj (n : ℕ) (env : ℕ → ℝ) : ℕ → ℕ → ℝ := fun k j => env (k * n + j)

lemma stepEnv_envTraj (n : ℕ) (env : ℕ → ℝ) : stepEnv n (envTraj n env) env 0 = env := by
  funext j
  simp only [stepEnv, envTraj]
  split_ifs <;> congr 1 <;> simp <;> omega

/-- **Meaning of `REFUTED` (`del_equations`).** The certificate's point is a three-level
discrete sequence `(q0, q1, q2)` in `D` at which the real DEL equations and the claimed
update disagree: it is a trajectory of one and not of the other. -/
theorem del_refuted_meaning {n : ℕ} {Ld : Expr} {D : (ℕ → ℝ) → Prop} {cs : List Law}
    (hcert : DELRefuted n Ld D cs) (hacc : NoAccel n Ld) :
    ∃ env, D env ∧ stepEnv n (envTraj n env) env 0 = env ∧
      ¬((∀ i < n, realDEL n i Ld (envTraj n env) env 0 = 0) ↔ Claims cs env) := by
  obtain ⟨env, hD, hok, _, _, hne⟩ := hcert
  refine ⟨env, hD, stepEnv_envTraj n env, ?_⟩
  have hok' : StepOK n Ld (stepEnv n (envTraj n env) env 0) := by rw [stepEnv_envTraj]; exact hok
  intro h
  apply hne
  rw [← h]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [DEL_bridge hi hacc _ env 0 hok', stepEnv_envTraj]

/-! ### `discrete_momentum_conserved`: discrete Noether, certificate form -/

/-- `Σ_i μ_i · DEL n (k + i) L_d` over the list `mus`, starting at index `k`. -/
noncomputable def delSum (n : ℕ) (Ld : Expr) (env : ℕ → ℝ) : ℕ → List Expr → ℝ
  | _, [] => 0
  | k, m :: ms => m.eval env * (DEL n k Ld).eval env + delSum n Ld env (k + 1) ms

lemma delSum_eq_zero (n : ℕ) (Ld : Expr) (env : ℕ → ℝ) :
    ∀ (ms : List Expr) (k : ℕ), (∀ i < ms.length, (DEL n (k + i) Ld).eval env = 0) →
      delSum n Ld env k ms = 0
  | [], _, _ => rfl
  | m :: ms, k, h => by
      have h0 := h 0 (by simp)
      have ih := delSum_eq_zero n Ld env ms (k + 1) fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this
      simp only [delSum, ih, add_zero]
      simp at h0
      rw [h0, mul_zero]

/-- What a `VERIFIED` discrete-momentum certificate proves (the judge writes it with concrete
`n L_d D J`, `∃ mus` with `mus.length = n`, and `NoAccel` of `L_d` and `J`). -/
def DMomentumVerified (n : ℕ) (Ld : Expr) (D : (ℕ → ℝ) → Prop) (J : Expr) (mus : List Expr) :
    Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → StepOK n Ld env ∧ Ld.physOK env ∧ (Ld.ren (shift n)).physOK env ∧
      J.physOK env ∧ (J.ren (shift n)).physOK env ∧ (∀ m ∈ mus, m.physOK env) ∧
      (J.ren (shift n)).eval env - J.eval env = delSum n Ld env 0 mus

/-- `∂DEL/∂q2` is a real derivative at the point and is invertible: `q2` is the step taken
from `(q0, q1)` (locally unique, by the implicit function theorem, not formalised here). -/
def RegularStep (n : ℕ) (Ld : Expr) (env : ℕ → ℝ) : Prop :=
  (∀ i < n, (DEL n i Ld).diffOK env) ∧
    (Matrix.of fun i j : Fin n => ((DEL n i Ld).deriv (2 * n + j)).eval env).det ≠ 0

/-- What a `REFUTED` discrete-momentum certificate proves. -/
def DMomentumRefuted (n : ℕ) (Ld : Expr) (D : (ℕ → ℝ) → Prop) (J : Expr) : Prop :=
  ∃ env, D env ∧ StepOK n Ld env ∧ Ld.physOK env ∧ (Ld.ren (shift n)).physOK env ∧
    J.physOK env ∧ (J.ren (shift n)).physOK env ∧ DELSystem n Ld env ∧ RegularStep n Ld env ∧
    (J.ren (shift n)).eval env ≠ J.eval env

/-- **Meaning of `VERIFIED` (discrete Noether).** Let `q_0, …, q_{N+1}` be a discrete
trajectory: every triple `(q_k, q_{k+1}, q_{k+2})`, `k < N`, is in `D` and satisfies the real
DEL equations. Then `J(q_N, q_{N+1}) = J(q_0, q_1)`, exactly. -/
theorem dmomentum_meaning {n : ℕ} {Ld J : Expr} {D : (ℕ → ℝ) → Prop} {mus : List Expr}
    (hcert : DMomentumVerified n Ld D J mus) (hlen : mus.length = n)
    (hacc : NoAccel n Ld) (hJ : NoAccel n J) (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k < N, D (stepEnv n q p k)) → (∀ k < N, ∀ i < n, realDEL n i Ld q p k = 0) →
      J.eval (stepEnv n q p N) = J.eval (stepEnv n q p 0)
  | 0, _, _ => rfl
  | N + 1, hD, hDEL => by
      have ih := dmomentum_meaning hcert hlen hacc hJ q p N (fun k hk => hD k (by omega))
        (fun k hk => hDEL k (by omega))
      obtain ⟨hok, _, _, _, _, _, hid⟩ := hcert.2 _ (hD N (by omega))
      have h0 : delSum n Ld (stepEnv n q p N) 0 mus = 0 :=
        delSum_eq_zero n Ld _ mus 0 fun i hi => by
          rw [zero_add, ← DEL_bridge (by omega) hacc q p N hok]
          exact hDEL N (by omega) i (by omega)
      rw [← ih, ← eval_ren_shift hJ q p N]
      linarith

/-- **Meaning of `REFUTED` (discrete momentum).** The certificate's point is a three-level
discrete trajectory `(q0, q1, q2)` in `D`: it satisfies the real DEL equations, `q2` is a
regular step from `(q0, q1)`, and `J(q1, q2) ≠ J(q0, q1)`. -/
theorem dmomentum_refuted_meaning {n : ℕ} {Ld J : Expr} {D : (ℕ → ℝ) → Prop}
    (hcert : DMomentumRefuted n Ld D J) (hacc : NoAccel n Ld) (hJ : NoAccel n J) :
    ∃ env, D env ∧ RegularStep n Ld env ∧ stepEnv n (envTraj n env) env 0 = env ∧
      (∀ i < n, realDEL n i Ld (envTraj n env) env 0 = 0) ∧
      J.eval (stepEnv n (envTraj n env) env 1) ≠ J.eval (stepEnv n (envTraj n env) env 0) := by
  obtain ⟨env, hD, hok, _, _, _, _, hsys, hreg, hne⟩ := hcert
  have hok' : StepOK n Ld (stepEnv n (envTraj n env) env 0) := by rw [stepEnv_envTraj]; exact hok
  refine ⟨env, hD, hreg, stepEnv_envTraj n env, fun i hi => ?_, ?_⟩
  · rw [DEL_bridge hi hacc _ env 0 hok', stepEnv_envTraj]; exact hsys i hi
  · rw [← eval_ren_shift hJ, stepEnv_envTraj]; exact hne

end PhysVerify
