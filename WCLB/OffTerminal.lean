import WC.SourceGrouping
import WC.ChainBandBudget
import WCLB.Certificates

/-! Lemma 9(iii): the complete subdifferential away from the inactive set. -/

noncomputable section
namespace WCLB
open WC

/-- If the distance from the all-scores-nonpositive set exceeds the paper's
radius, every Fréchet subgradient of the Lipschitz majorant has the stated norm.
One additional group of source distances suffices when the near radius is
reduced from `1/(288√N)` to `1/(360√N)`. -/
theorem off_terminal_subgradient_lower {M N : ℕ} (hN : 256 ≤ N)
    (hM : M ≤ 2 ^ (8 * N)) {z g : ChainSpace M N}
    (hfar : 1 / (360 * Real.sqrt (N : ℝ)) <
      Metric.infDist z (inactiveSet M N))
    (hg : g ∈ subdifferential chainMajorant z) :
    1 / Real.sqrt (98 * (N : ℝ)) ≤ ‖g‖ := by
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNp
  have hs := Real.sqrt_pos.mpr hn
  let r : ℝ := 1 / (360 * Real.sqrt (N : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : r ≤ chainNearRadius N := by
    dsimp [r, chainNearRadius]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hbound : chainNearRadius N ≤ 8 * r := by
    dsimp [r, chainNearRadius]
    field_simp
    nlinarith
  have hcover : chainSourceRadius M N ≤ (8 : ℝ) ^ (3 * N + 1) * r := calc
    _ ≤ (8 : ℝ) ^ (3 * N) * chainNearRadius N := by
      simpa [chainNearRadius, div_eq_mul_inv] using chain_source_radius_threeN_coverage hN hM
    _ ≤ (8 : ℝ) ^ (3 * N) * (8 * r) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [pow_succ]; ring
  have hdist (q : ChainSpace M N) (hq : q ∈ terminalRegion) : r < ‖z - q‖ := by
    have hi := Metric.infDist_le_dist_of_mem (x := z)
      (show q ∈ inactiveSet M N from
        terminalRegion_scores_nonpos hNp hq)
    simpa only [dist_eq_norm] using hfar.trans_le hi
  have hsq := chainMajorant_subgradient_norm_sq_lower_of_radius hN hr hsmall z hcover hdist hg
  have hden : 25 * (N : ℝ) + 8 * ((3 * N + 1 : ℕ) : ℝ) ≤ 98 * N := by
    push_cast
    have : (256 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  apply (sq_le_sq₀ (by positivity) (norm_nonneg g)).mp
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  exact (one_div_le_one_div_of_le (by positivity) hden).trans hsq

end WCLB
