import PhysVerify.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit update maps: `update_conserves`

An integrator given as an explicit map `z' = Φ(z; h, params)` on the state `z`, with no
variational structure assumed. Variable layout (n state components, k < n):

| variable | index |
|----------|-------|
| `z_k` (state) | `k` |
| `h`, parameters | `n, n+1, …` |

`Phi : List Expr` holds `Φ_0 … Φ_{n−1}`, each evaluated at the *old* state (a simultaneous
update). `updateStep Phi env` is the new environment: coordinate `k < Phi.length` becomes
`Φ_k(env)`, every other coordinate (`h`, the parameters) is unchanged (`updateStep_of_ge`).

Main results:

* `update_conserves_meaning`: if on `D`, `J(Φ(z)) = J(z)` as an identity (`UpdateVerified`),
  then along every orbit `z_{k+1} = Φ(z_k)` whose points `z_0 … z_{N−1}` lie in `D`,
  `J(z_N) = J(z_0)` exactly.
* `update_refuted_meaning`: a point `z ∈ D` with `J(Φ(z)) ≠ J(z)` is the start of an orbit on
  which `J` changes at the first step. Because `Φ` is explicit, every point is on an orbit: no
  regularity condition (no implicit-function step) is needed, unlike `DMomentumRefuted`.

Lean totalises `x/0`, `sqrt` and `log` of negatives. Both certificates require `physOK` (no
junk values) of every `Φ_k` and of `J` at `z`, and of `J` at `Φ(z)`, and `VERIFIED` requires a
point of `D` (so it is never vacuous).
-/

namespace PhysVerify
open Expr

/-- Write `Φ_i(env)` into coordinate `k + i` of `acc`, every `Φ_i` evaluated at `env`. -/
noncomputable def updAux (env : ℕ → ℝ) : List Expr → ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], _, acc => acc
  | e :: es, k, acc => updAux env es (k + 1) (Function.update acc k (e.eval env))

/-- One step of the explicit map: coordinate `k < Phi.length` becomes `Φ_k(env)`. -/
noncomputable def updateStep (Phi : List Expr) (env : ℕ → ℝ) : ℕ → ℝ := updAux env Phi 0 env

lemma updAux_of_ge (env : ℕ → ℝ) :
    ∀ (es : List Expr) (k : ℕ) (acc : ℕ → ℝ) (j : ℕ), k + es.length ≤ j → updAux env es k acc j = acc j
  | [], _, _, _, _ => rfl
  | e :: es, k, acc, j, hj => by
      simp only [List.length_cons] at hj
      rw [updAux, updAux_of_ge env es (k + 1) _ j (by omega), Function.update_of_ne (by omega)]

/-- The map changes only the state: `h` and the parameters are carried along unchanged. -/
theorem updateStep_of_ge (Phi : List Expr) (env : ℕ → ℝ) (j : ℕ) (hj : Phi.length ≤ j) :
    updateStep Phi env j = env j :=
  updAux_of_ge env Phi 0 env j (by omega)

/-- Every component has the dimension of the state variable it overwrites. -/
def UpdDims (ctx : List Dim) : List Expr → ℕ → Bool
  | [], _ => true
  | e :: es, k => ((e.dimOf ctx).isSome && decide (e.dimOf ctx = (Expr.var k).dimOf ctx)) &&
      UpdDims ctx es (k + 1)

/-- No junk values in the map or in `J`, before and after the step. -/
def UpdateOK (Phi : List Expr) (J : Expr) (env : ℕ → ℝ) : Prop :=
  (∀ e ∈ Phi, e.physOK env) ∧ J.physOK env ∧ J.physOK (updateStep Phi env)

/-- What a `VERIFIED` `update_conserves` certificate proves. -/
def UpdateVerified (Phi : List Expr) (D : (ℕ → ℝ) → Prop) (J : Expr) : Prop :=
  (∃ env, D env) ∧
    ∀ env, D env → UpdateOK Phi J env ∧ J.eval (updateStep Phi env) = J.eval env

/-- What a `REFUTED` `update_conserves` certificate proves. -/
def UpdateRefuted (Phi : List Expr) (D : (ℕ → ℝ) → Prop) (J : Expr) : Prop :=
  ∃ env, D env ∧ UpdateOK Phi J env ∧ J.eval (updateStep Phi env) ≠ J.eval env

/-- **Meaning of `VERIFIED` (`update_conserves`).** Along every orbit `z_{k+1} = Φ(z_k)` whose
points `z_0 … z_{N−1}` lie in `D`, `J(z_N) = J(z_0)`, exactly. -/
theorem update_conserves_meaning {Phi : List Expr} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : UpdateVerified Phi D J) (z : ℕ → ℕ → ℝ) (hz : ∀ k, z (k + 1) = updateStep Phi (z k)) :
    ∀ N : ℕ, (∀ k < N, D (z k)) → J.eval (z N) = J.eval (z 0)
  | 0, _ => rfl
  | N + 1, hD => by
      rw [hz N, (hcert.2 _ (hD N (by omega))).2]
      exact update_conserves_meaning hcert z hz N fun k hk => hD k (by omega)

/-- A `VERIFIED` certificate is never vacuous. -/
theorem update_verified_nonempty {Phi : List Expr} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : UpdateVerified Phi D J) : ∃ env, D env ∧ UpdateOK Phi J env :=
  let ⟨env, h⟩ := hcert.1
  ⟨env, h, (hcert.2 env h).1⟩

/-- **Meaning of `REFUTED` (`update_conserves`).** The orbit `z_k = Φ^k(z_0)` of the
certificate's point starts in `D` and `J(z_1) ≠ J(z_0)`. -/
theorem update_refuted_meaning {Phi : List Expr} {D : (ℕ → ℝ) → Prop} {J : Expr}
    (hcert : UpdateRefuted Phi D J) :
    ∃ z : ℕ → ℕ → ℝ, (∀ k, z (k + 1) = updateStep Phi (z k)) ∧ D (z 0) ∧ UpdateOK Phi J (z 0) ∧
      J.eval (z 1) ≠ J.eval (z 0) := by
  obtain ⟨env, hD, hok, hne⟩ := hcert
  refine ⟨fun k => (updateStep Phi)^[k] env, fun k => ?_, hD, hok, hne⟩
  exact Function.iterate_succ_apply' (updateStep Phi) k env

end PhysVerify
