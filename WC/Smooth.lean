import WC.Subgradient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv

/-! A genuine analytic smoothness-to-weak-convexity theorem, used for the
progress and activation terms in the coupled construction. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weaklyConvex_of_lipschitz_derivative {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) : WeaklyConvex L f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let d := y - x
  let φ : ℝ → ℝ := fun t => f (x + t • d) + L / 2 * ‖x + t • d‖ ^ 2
  let φ' : ℝ → ℝ := fun t => inner ℝ (g (x + t • d)) d + L * inner ℝ (x + t • d) d
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • d) d t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const d).const_add x
  have hφ (t : ℝ) : HasDerivAt φ (φ' t) t := by
    have hbase := (hf (x + t • d)).comp_hasDerivAt t (hpath t)
    have hquad := ((hpath t).norm_sq).const_mul (L / 2)
    convert hbase.add hquad using 1
    all_goals try rfl
    all_goals try dsimp [φ, φ']
    all_goals try simp only [innerSL_apply_apply]
    all_goals ring
  have hmono : Monotone φ' := by
    intro s t hst
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    have hnorm := hg (x + t • d) (x + s • d)
    have hpathdiff : (x + t • d) - (x + s • d) = (t - s) • d := by module
    rw [hpathdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hts] at hnorm
    have hinner := neg_le_of_abs_le (abs_real_inner_le_norm
      (g (x + t • d) - g (x + s • d)) d)
    have hmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
    simp only [inner_sub_left] at hinner
    dsimp [φ']
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith
  have hconv : ConvexOn ℝ Set.univ φ :=
    Monotone.convexOn_univ_of_deriv (fun t => (hφ t).differentiableAt)
      (by simpa only [funext (fun t => (hφ t).deriv)] using hmono)
  have hline := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  have hcombo : x + b • d = a • x + b • y := by
    have ha' : a = 1 - b := by linarith
    rw [ha']
    dsimp [d]
    module
  simpa only [φ, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, one_smul,
    add_zero, d, add_sub_cancel, hcombo] using hline

end WC
