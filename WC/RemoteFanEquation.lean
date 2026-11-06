import WC.RemoteFacet

/-! The exact pure-fan displacement equation at an actual remote source. -/

noncomputable section
namespace WC

theorem remote_source_positive_scores {M N : ℕ} (hN : 0 < N)
    {z y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 z) (hzy : z ≠ y) :
    0 < ‖positiveCoupledScores y‖ := by
  by_contra h
  have hzero : ‖positiveCoupledScores y‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
  have hterm := (positiveCoupledScores_norm_eq_zero_iff_terminalRegion hN y).mp hzero
  have hmin := (coupledFunction_eq_minimum_iff_terminalRegion hN y).mpr hterm
  change coupledFunction y - 2 * ‖z - y‖ = chainMajorant z at hy
  rw [hmin] at hy
  have hbound := chainMajorant_lower_bound hN z
  have hnorm : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
  linarith

theorem remote_source_pure_fan_displacement {M N : ℕ} (hN : 0 < N)
    {z y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 z) (hzy : z ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (hactive : coupledFacetBranch w a y = coupledFunction y) (m : Fin M) (n : Fin N)
    (ha : a m = some n) (hp : progressGradient (euclideanBlock y m) n = 0) :
    z (m, n) - y (m, n) = ‖z - y‖ * w m / 8 := by
  have hg := coupledFacetBranchGradient_mem_subdifferential hN w hw a y hactive
  have hremote := chain_remote_source_subgradient hN hy hzy hg
  have hc := congrArg (fun v : ChainSpace M N => v (m, n)) hremote
  rw [coupledFacetBranchGradient_apply] at hc
  simp only [blockFacetGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ha,
    affineFacetGradient, PiLp.single_eq_same, smoothBlockGradient, hp, mul_zero, add_zero, PiLp.sub_apply] at hc
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
  have hcoeff : (2 / (N : ℝ)) * (w m * (-(N : ℝ) / 8)) = -(w m) / 4 := by field_simp; ring
  rw [hcoeff] at hc
  field_simp at hc
  nlinarith

end WC
