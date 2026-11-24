import PhysVerify.Expr

/-!
# Orbit-existence checks (step 6)

Weak-anthropic "existence facts" phrased as weakly as possible: we do not ask for closed
orbits (Bertrand) or stability, only that the observed body's distance `r(t)` has a local
minimum (perihelion) and a local maximum (aphelion).

For Newtonian motion in a central field with attractive acceleration magnitude `f(r)`, the
radial equation is `r'' = ℓ²/r³ − f(r)`. At a local minimum `r'' ≥ 0` and at a local
maximum `r'' ≤ 0`, hence with `h(r) = r³ f(r)`:

    h(r_peri) ≤ ℓ² ≤ h(r_aph).

So a force law with `h(r_aph) < h(r_peri)` for every perihelion/aphelion consistent with
the observations cannot produce the observed orbit, for any angular momentum ℓ.
-/

open Set Filter Topology

namespace PhysVerify

/-- At a local minimum of `r`, the second derivative is non-negative. -/
theorem IsLocalMin.second_deriv_nonneg {r r' : ℝ → ℝ} {t₀ c : ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : HasDerivAt r' c t₀) (hmin : IsLocalMin r t₀) :
    0 ≤ c := by
  by_contra hc
  push_neg at hc
  have h0 : r' t₀ = 0 := hmin.hasDerivAt_eq_zero (hr t₀)
  -- the slope of r' at t₀ tends to c < 0, so r' < 0 just to the right of t₀
  have hslope : Tendsto (slope r' t₀) (𝓝[>] t₀) (𝓝 c) :=
    (hasDerivAt_iff_tendsto_slope.1 hr').mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  have hneg : ∀ᶠ t in 𝓝[>] t₀, r' t < 0 := by
    filter_upwards [hslope.eventually (gt_mem_nhds hc), self_mem_nhdsWithin] with t ht htt
    rw [slope_def_field, h0, sub_zero] at ht
    exact (div_neg_iff.mp ht).resolve_left (fun h => absurd h.2 (not_lt.mpr (by
      have : 0 < t - t₀ := sub_pos.mpr htt; linarith))) |>.1
  have hle : ∀ᶠ t in 𝓝[>] t₀, r t₀ ≤ r t := nhdsWithin_le_nhds hmin
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hneg.and hle)
  have hu' : t₀ < u := hu
  -- pick t in (t₀, u); the mean value theorem on [t₀, t] gives r t < r t₀
  set t := (t₀ + u) / 2
  have ht : t ∈ Ioo t₀ u := ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope r r' ht.1
    (fun x _ => (hr x).continuousAt.continuousWithinAt) (fun x _ => hr x)
  have hξneg : r' ξ < 0 := (hsub ⟨hξ.1, hξ.2.trans ht.2⟩).1
  have hrt : r t₀ ≤ r t := (hsub ht).2
  rw [hξeq, div_neg_iff] at hξneg
  rcases hξneg with ⟨_, h⟩ | ⟨h, _⟩
  · linarith [ht.1]
  · linarith

theorem IsLocalMax.second_deriv_nonpos {r r' : ℝ → ℝ} {t₀ c : ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : HasDerivAt r' c t₀) (hmax : IsLocalMax r t₀) :
    c ≤ 0 := by
  have := IsLocalMin.second_deriv_nonneg (r := fun t => -r t) (r' := fun t => -r' t)
    (fun t => (hr t).neg) hr'.neg hmax.neg
  linarith

/-- **Turning points.** Radial motion `r'' = ℓ²/r³ − f(r)` with a perihelion at `t₁` and an
aphelion at `t₂` satisfies `h(r(t₁)) ≤ ℓ² ≤ h(r(t₂))` where `h(r) = r³ f(r)`. -/
theorem turning_points {r v f : ℝ → ℝ} {ℓ t₁ t₂ : ℝ}
    (hr : ∀ t, HasDerivAt r (v t) t) (hv : ∀ t, HasDerivAt v (ℓ ^ 2 / r t ^ 3 - f (r t)) t)
    (hpos : ∀ t, 0 < r t) (h₁ : IsLocalMin r t₁) (h₂ : IsLocalMax r t₂) :
    r t₁ ^ 3 * f (r t₁) ≤ ℓ ^ 2 ∧ ℓ ^ 2 ≤ r t₂ ^ 3 * f (r t₂) := by
  have c₁ := IsLocalMin.second_deriv_nonneg hr (hv t₁) h₁
  have c₂ := IsLocalMax.second_deriv_nonpos hr (hv t₂) h₂
  have p₁ := pow_pos (hpos t₁) 3
  have p₂ := pow_pos (hpos t₂) 3
  rw [sub_nonneg, le_div_iff₀ p₁] at c₁
  rw [sub_nonpos, div_le_iff₀ p₂] at c₂
  constructor <;> linarith

/-- `h(r) = r³ f(r)` as an expression (radius = variable `k`). -/
def hExpr (e : Expr) (k : ℕ) : Expr := .mul (.powi (.var k) 3) e

lemma hExpr_eval (e : Expr) (k : ℕ) (env : ℕ → ℝ) (x : ℝ) :
    (hExpr e k).eval (Function.update env k x) = x ^ 3 * e.eval (Function.update env k x) := by
  simp only [hExpr, Expr.eval, Function.update_self, zpow_ofNat]

/-- The certificate obligation: for every perihelion `x ∈ [a₁,b₁]` and aphelion
`y ∈ [a₂,b₂]` allowed by the data, `h(y) < h(x)` for the force law `e` (radius = var `k`). -/
def EccentricExcluded (e : Expr) (k : ℕ) (env : ℕ → ℝ) (a₁ b₁ a₂ b₂ : ℝ) : Prop :=
  ∀ x ∈ Icc a₁ b₁, ∀ y ∈ Icc a₂ b₂,
    (hExpr e k).eval (Function.update env k y) < (hExpr e k).eval (Function.update env k x)

/-- **Refutation by orbit existence.** If the certificate obligation holds, no radial
trajectory of the force law (any angular momentum) has a perihelion in `[a₁,b₁]` and an
aphelion in `[a₂,b₂]`. -/
theorem EccentricExcluded.refutes {e : Expr} {k : ℕ} {env : ℕ → ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hx : EccentricExcluded e k env a₁ b₁ a₂ b₂) {r v : ℝ → ℝ} {ℓ t₁ t₂ : ℝ}
    (hr : ∀ t, HasDerivAt r (v t) t)
    (hv : ∀ t, HasDerivAt v (ℓ ^ 2 / r t ^ 3 - e.eval (Function.update env k (r t))) t)
    (hpos : ∀ t, 0 < r t) (h₁ : IsLocalMin r t₁) (h₂ : IsLocalMax r t₂)
    (hr₁ : r t₁ ∈ Icc a₁ b₁) (hr₂ : r t₂ ∈ Icc a₂ b₂) : False := by
  have := turning_points (f := fun x => e.eval (Function.update env k x)) hr hv hpos h₁ h₂
  have := hx _ hr₁ _ hr₂
  rw [hExpr_eval, hExpr_eval] at this
  linarith

end PhysVerify
