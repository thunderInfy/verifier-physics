import PhysVerify.Expr
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-!
# Interval-bound certificates (step 3)

One lemma per `Expr` node. A planner proves `L ≤ e.eval env ∧ e.eval env ≤ U` bottom-up,
one `have` per subterm; each step is closed by one of these lemmas plus `norm_num` side
conditions on rational numbers. v1 covers non-negative magnitudes (the usual case for
measured physical quantities); anything else is left to other strategies.
-/

namespace PhysVerify

/-- `x ∈ [L, U]` -/
abbrev Bnd (L x U : ℝ) : Prop := L ≤ x ∧ x ≤ U

namespace Bnd
variable {env : ℕ → ℝ}

lemma var {i : ℕ} {L U : ℝ} (h : Bnd L (env i) U) : Bnd L ((Expr.var i).eval env) U := h

lemma lit (q : ℚ) {L U : ℝ} (hL : L ≤ q) (hU : (q : ℝ) ≤ U) :
    Bnd L ((Expr.lit q).eval env) U := ⟨hL, hU⟩

lemma pi {L U : ℝ} (hL : L ≤ 3.141592) (hU : 3.141593 ≤ U) : Bnd L (Expr.pi.eval env) U :=
  ⟨by simp only [Expr.eval]; linarith [Real.pi_gt_d6],
   by simp only [Expr.eval]; linarith [Real.pi_lt_d6]⟩

lemma neg {a : Expr} {la ua L U : ℝ} (h : Bnd la (a.eval env) ua) (hL : L ≤ -ua) (hU : -la ≤ U) :
    Bnd L ((Expr.neg a).eval env) U := by
  simp only [Expr.eval]; constructor <;> linarith [h.1, h.2]

lemma add {a b : Expr} {la ua lb ub L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hb : Bnd lb (b.eval env) ub) (hL : L ≤ la + lb) (hU : ua + ub ≤ U) :
    Bnd L ((Expr.add a b).eval env) U := by
  simp only [Expr.eval]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma sub {a b : Expr} {la ua lb ub L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hb : Bnd lb (b.eval env) ub) (hL : L ≤ la - ub) (hU : ua - lb ≤ U) :
    Bnd L ((Expr.sub a b).eval env) U := by
  simp only [Expr.eval]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma mul {a b : Expr} {la ua lb ub L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hb : Bnd lb (b.eval env) ub) (hla : 0 ≤ la) (hlb : 0 ≤ lb)
    (hL : L ≤ la * lb) (hU : ua * ub ≤ U) : Bnd L ((Expr.mul a b).eval env) U := by
  simp only [Expr.eval]
  exact ⟨hL.trans (mul_le_mul ha.1 hb.1 hlb (hla.trans ha.1)),
    (mul_le_mul ha.2 hb.2 (hlb.trans hb.1) ((hla.trans ha.1).trans ha.2)).trans hU⟩

lemma div {a b : Expr} {la ua lb ub L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hb : Bnd lb (b.eval env) ub) (hla : 0 ≤ la) (hlb : 0 < lb)
    (hL : L ≤ la / ub) (hU : ua / lb ≤ U) : Bnd L ((Expr.div a b).eval env) U := by
  simp only [Expr.eval]
  have hb0 : 0 < b.eval env := hlb.trans_le hb.1
  have ha0 : 0 ≤ a.eval env := hla.trans ha.1
  exact ⟨hL.trans (div_le_div₀ ha0 ha.1 hb0 hb.2),
    (div_le_div₀ ((hla.trans ha.1).trans ha.2) ha.2 hlb hb.1).trans hU⟩

lemma powi_nonneg {a : Expr} {n : ℤ} {la ua L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hla : 0 ≤ la) (hn : 0 ≤ n) (hL : L ≤ la ^ n) (hU : ua ^ n ≤ U) :
    Bnd L ((Expr.powi a n).eval env) U := by
  simp only [Expr.eval]
  exact ⟨hL.trans (zpow_le_zpow_left₀ hn hla ha.1),
    (zpow_le_zpow_left₀ hn (hla.trans ha.1) ha.2).trans hU⟩

lemma powi_neg {a : Expr} {n : ℤ} {la ua L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hla : 0 < la) (hn : n < 0) (hL : L ≤ ua ^ n) (hU : la ^ n ≤ U) :
    Bnd L ((Expr.powi a n).eval env) U := by
  simp only [Expr.eval]
  have hx : 0 < a.eval env := hla.trans_le ha.1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
  simp only [zpow_neg] at hL hU ⊢
  constructor
  · refine hL.trans (inv_anti₀ (zpow_pos hx _) (zpow_le_zpow_left₀ (by omega) hx.le ha.2))
  · refine (inv_anti₀ (zpow_pos hla _) (zpow_le_zpow_left₀ (by omega) hla.le ha.1)).trans hU

lemma sqrt {a : Expr} {la ua L U : ℝ} (ha : Bnd la (a.eval env) ua)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ la) (hU0 : 0 ≤ U) (hU : ua ≤ U ^ 2) :
    Bnd L ((Expr.sqrt a).eval env) U := by
  simp only [Expr.eval]
  constructor
  · exact Real.le_sqrt_of_sq_le (hL.trans ha.1) |>.trans' le_rfl
  · exact Real.sqrt_le_iff.mpr ⟨hU0, ha.2.trans hU⟩

/-- Two quantities forced equal by a law cannot lie in disjoint intervals. -/
lemma disjoint {x y Lx Ux Ly Uy : ℝ} (hx : Bnd Lx x Ux) (hy : Bnd Ly y Uy) (heq : x = y)
    (hsep : Ux < Ly ∨ Uy < Lx) : False := by
  rcases hsep with h | h <;> linarith [hx.1, hx.2, hy.1, hy.2]

end Bnd
end PhysVerify
