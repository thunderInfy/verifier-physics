import PhysVerify.Update

/-!
# Straight-line kernels: `exec` semantics and `update_conserves`

A kernel is one time step written as a straight-line program: an ordered list of
assignments `x := e`, where `x` is a variable index (a state variable or a temporary) and
`e` is an `Expr` over the *current* values. No loops, branches, arrays or pointers. Variable
layout (n state components, m parameters including `h`):

| variable | index |
|----------|-------|
| `z_k` (state) | `k < n` |
| `h`, parameters | `n, n+1, …` (sorted by name) |
| temporaries | `n + m, …` (in order of first assignment) |

`exec prog env` runs the assignments in order, each evaluated in the environment the previous
ones produced (`exec_cons`). This is the semantics of the C the judge emits from the same
program (`physverify/kernel_c.py`); the C printer and compiler are not covered by any theorem
here.

Main results:

* `kernel_conserves_meaning`: if on `D`, `J(exec prog z) = J(z)` (`KernelVerified`), then along
  every orbit `z_{k+1} = exec prog z_k` whose points `z_0 … z_{N−1}` lie in `D`,
  `J(z_N) = J(z_0)` exactly. `D` and `J` must not mention the temporaries (the judge checks
  that), so their values at the start of a step do not matter.
* `kernel_refuted_meaning`: a point `z ∈ D` with `J(exec prog z) ≠ J(z)` starts an orbit on
  which `J` changes at the first step.
* `exec_of_not_mem`: a variable no assignment writes (`h`, the parameters) is unchanged.

Junk-freeness is stated per step (`ExecOK`): every assigned expression is `physOK` in the
environment where it is evaluated. A temporary that is computed and then never used still has
to be junk-free, which a check on the composed map would miss.
-/

namespace PhysVerify
open Expr

/-- A straight-line program: assignments `(x, e)` meaning `x := e`, run in order. -/
abbrev Prog := List (ℕ × Expr)

/-- Run the assignments in order; each is evaluated in the current environment. -/
noncomputable def exec : Prog → (ℕ → ℝ) → (ℕ → ℝ)
  | [], env => env
  | (x, e) :: ps, env => exec ps (Function.update env x (e.eval env))

@[simp] lemma exec_nil (env : ℕ → ℝ) : exec [] env = env := rfl

lemma exec_cons (x : ℕ) (e : Expr) (ps : Prog) (env : ℕ → ℝ) :
    exec ((x, e) :: ps) env = exec ps (Function.update env x (e.eval env)) := rfl

/-- A variable that no assignment writes keeps its value. -/
theorem exec_of_not_mem : ∀ (prog : Prog) (env : ℕ → ℝ) (j : ℕ),
    j ∉ prog.map Prod.fst → exec prog env j = env j
  | [], _, _, _ => rfl
  | (x, e) :: ps, env, j, hj => by
      simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [exec_cons, exec_of_not_mem ps _ j hj.2, Function.update_of_ne hj.1]

/-- No junk value at any step: each assigned expression is `physOK` where it is evaluated. -/
def ExecOK : Prog → (ℕ → ℝ) → Prop
  | [], _ => True
  | (x, e) :: ps, env => e.physOK env ∧ ExecOK ps (Function.update env x (e.eval env))

/-- Every assignment is well-dimensioned and has the dimension of the variable it writes. -/
def ProgDims (ctx : List Dim) : Prog → Bool
  | [] => true
  | (x, e) :: ps => ((e.dimOf ctx).isSome && decide (e.dimOf ctx = (Expr.var x).dimOf ctx)) &&
      ProgDims ctx ps

/-- No junk values in the program's steps or in `J`, before and after the step. -/
def KernelOK (prog : Prog) (J : Expr) (env : ℕ → ℝ) : Prop :=
  ExecOK prog env ∧ J.physOK env ∧ J.physOK (exec prog env)

/-- What a `VERIFIED` `update_conserves` certificate for a kernel proves. -/
def KernelVerified (prog : Prog) (D : (ℕ → ℝ) → Prop) (J : Expr) : Prop :=
  (∃ env, D env) ∧ ∀ env, D env → KernelOK prog J env ∧ J.eval (exec prog env) = J.eval env

/-- What a `REFUTED` `update_conserves` certificate for a kernel proves. -/
def KernelRefuted (prog : Prog) (D : (ℕ → ℝ) → Prop) (J : Expr) : Prop :=
  ∃ env, D env ∧ KernelOK prog J env ∧ J.eval (exec prog env) ≠ J.eval env

/-- Any map `F` with `J ∘ F = J` on `D` conserves `J` along orbits that stay in `D`. -/
theorem orbit_conserves {F : (ℕ → ℝ) → (ℕ → ℝ)} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hF : ∀ env, D env → J.eval (F env) = J.eval env) (z : ℕ → ℕ → ℝ)
    (hz : ∀ k, z (k + 1) = F (z k)) : ∀ N : ℕ, (∀ k < N, D (z k)) → J.eval (z N) = J.eval (z 0)
  | 0, _ => rfl
  | N + 1, hD => by
      rw [hz N, hF _ (hD N (by omega))]
      exact orbit_conserves hF z hz N fun k hk => hD k (by omega)

/-- **Meaning of `VERIFIED` (`update_conserves`, kernel).** Along every orbit
`z_{k+1} = exec prog z_k` whose points `z_0 … z_{N−1}` lie in `D`, `J(z_N) = J(z_0)`, exactly. -/
theorem kernel_conserves_meaning {prog : Prog} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : KernelVerified prog D J) (z : ℕ → ℕ → ℝ) (hz : ∀ k, z (k + 1) = exec prog (z k)) :
    ∀ N : ℕ, (∀ k < N, D (z k)) → J.eval (z N) = J.eval (z 0) :=
  orbit_conserves (fun env h => (hcert.2 env h).2) z hz

/-- A `VERIFIED` kernel certificate is never vacuous. -/
theorem kernel_verified_nonempty {prog : Prog} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : KernelVerified prog D J) : ∃ env, D env ∧ KernelOK prog J env :=
  let ⟨env, h⟩ := hcert.1
  ⟨env, h, (hcert.2 env h).1⟩

/-- **Meaning of `REFUTED` (`update_conserves`, kernel).** The orbit `z_k = (exec prog)^[k] z_0`
of the certificate's point starts in `D`, takes no junk value in its first step, and
`J(z_1) ≠ J(z_0)`. -/
theorem kernel_refuted_meaning {prog : Prog} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : KernelRefuted prog D J) :
    ∃ z : ℕ → ℕ → ℝ, (∀ k, z (k + 1) = exec prog (z k)) ∧ D (z 0) ∧ KernelOK prog J (z 0) ∧
      J.eval (z 1) ≠ J.eval (z 0) := by
  obtain ⟨env, hD, hok, hne⟩ := hcert
  refine ⟨fun k => (exec prog)^[k] env, fun k => ?_, hD, hok, hne⟩
  exact Function.iterate_succ_apply' (exec prog) k env

end PhysVerify
