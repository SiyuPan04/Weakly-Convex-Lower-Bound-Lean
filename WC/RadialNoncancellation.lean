import WC.Basic

/-! The strict numerical margin preventing cancellation at a radial tie. -/

namespace WC

theorem radial_scalar_margin {k w : ℝ} (hk : 0 ≤ k) (hkmax : k ≤ 1 / 16)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (31 / 32 : ℝ) * k ≤ w ^ 2 * k + 9 * (1 - w) ^ 2 - w * (1 - w) * k / 16 := by
  have hksq := mul_nonneg hk (sub_nonneg.mpr hkmax)
  have hq := mul_nonneg hk (sq_nonneg (1 - w))
  have hs := sq_nonneg (2 * (1 - w) - 33 * k / 64)
  have hq0 := sq_nonneg (1 - w)
  nlinarith

theorem radial_vector_margin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h e : E} {k w : ℝ} (hk : 0 ≤ k) (hkmax : k ≤ 1 / 16)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (he : ‖e‖ = 1)
    (hh : k ≤ ‖h‖ ^ 2) (hinner : -k / 96 ≤ inner ℝ h e) :
    (31 / 32 : ℝ) * k ≤ ‖w • h + (3 * (1 - w)) • e‖ ^ 2 := by
  have hq : 0 ≤ 3 * (1 - w) := by linarith
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hw0, abs_of_nonneg hq, he, mul_one,
    real_inner_smul_left, real_inner_smul_right]
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg w)
  have hdot := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ 6 * w * (1 - w) by positivity)
  have hscalar := radial_scalar_margin hk hkmax hw0 hw1
  nlinarith

end WC
