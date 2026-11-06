import WC.Oracle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Constancy along a segment annihilated by every actual subgradient.
Quadratic support on both ends gives a quadratic modulus, hence zero
derivative and exact equality of function values. -/

noncomputable section
namespace WC
open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem segment_quadratic_modulus {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (x y : E)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ subdifferential f (x + t • (y - x)),
      inner ℝ v (y - x) = 0)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |f (x + s • (y - x)) - f (x + t • (y - x))| ≤
      (ρ / 2 * ‖y - x‖ ^ 2) * ‖s - t‖ ^ 2 := by
  obtain ⟨v, hv⟩ := subdifferential_nonempty (x + t • (y - x)) hG hρ hlip hwc
  obtain ⟨w, hw⟩ := subdifferential_nonempty (x + s • (y - x)) hG hρ hlip hwc
  have hvw := (weakSubgradient_iff_frechet hρ hwc).mpr hv
  have hww := (weakSubgradient_iff_frechet hρ hwc).mpr hw
  have hl := hvw (x + s • (y - x))
  have hu := hww (x + t • (y - x))
  have hst : (x + s • (y - x)) - (x + t • (y - x)) = (s - t) • (y - x) := by module
  have hts : (x + t • (y - x)) - (x + s • (y - x)) = (t - s) • (y - x) := by module
  rw [hst, real_inner_smul_right, hzero t ht v hv, mul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hl
  rw [hts, real_inner_smul_right, hzero s hs w hw, mul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hu
  rw [Real.norm_eq_abs, sq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (s - t), sq_nonneg (t - s)]

theorem constant_on_segment_of_subgradient_inner_zero {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (x y : E)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ subdifferential f (x + t • (y - x)),
      inner ℝ v (y - x) = 0) : f x = f y := by
  let φ : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hc : Continuous φ := (hlip.continuous hG).comp
    (continuous_const.add (continuous_id.smul continuous_const))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt φ 0 (Icc (0 : ℝ) 1) t := by
    rw [hasDerivWithinAt_iff_isLittleO]
    have hb : (fun s : ℝ => φ s - φ t - (s - t) • (0 : ℝ)) =O[𝓝[Icc (0 : ℝ) 1] t]
        (fun s : ℝ => ‖s - t‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound (ρ / 2 * ‖y - x‖ ^ 2)
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa only [φ, smul_zero, sub_zero, Real.norm_eq_abs, abs_pow, abs_abs] using
        segment_quadratic_modulus hG hρ hlip hwc x y hzero hs ht
    exact hb.trans_isLittleO ((Asymptotics.isLittleO_pow_sub_sub t (by norm_num : 1 < (2 : ℕ))).mono
      nhdsWithin_le_nhds)
  have heq := constant_of_has_deriv_right_zero hc.continuousOn
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    1 (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [φ, zero_smul, add_zero, one_smul, add_sub_cancel] using heq.symm

end WC
