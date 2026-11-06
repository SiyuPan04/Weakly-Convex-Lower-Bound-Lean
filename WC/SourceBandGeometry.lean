import WC.ChainSources
import WC.CoordinateLattice
import WC.SourceBandNumerics

/-! Actual coordinate exchanges prevent cancellation between remote sources
in one factor-eight radius band. -/

noncomputable section
namespace WC

theorem chain_source_lattice_comparison {M N : ℕ} (hN : 256 ≤ N)
    {z y y' : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 z)
    (hy' : y' ∈ majorantSources coupledFunction 2 z) :
    ‖z - y‖ + ‖z - y'‖ - ‖z - coordinateInf y y'‖ - ‖z - coordinateSup y y'‖ ≤
      (11 / 32 : ℝ) * ‖z - y‖ := by
  have hNpos : 0 < N := by omega
  have hfinite := chainMajorant_finite (M := M) hNpos
  have hmin := payoff_le_majorant hfinite z (coordinateInf y y')
  have hmax := payoff_le_majorant hfinite z (coordinateSup y y')
  change sourcePayoff coupledFunction 2 z y = lipschitzMajorant coupledFunction 2 z at hy
  change sourcePayoff coupledFunction 2 z y' = lipschitzMajorant coupledFunction 2 z at hy'
  have hcoord := chain_source_coord_le hNpos hy
  have hcoord' := chain_source_coord_le hNpos hy'
  have hdist := coordinateSup_distance_le hcoord hcoord'
  have hs₁ := (le_abs_self (positiveScoreTerm y - positiveScoreTerm (coordinateSup y y'))).trans
    (positiveScoreTerm_lipschitz_uniform hN y (coordinateSup y y'))
  rw [norm_sub_rev y (coordinateSup y y')] at hs₁
  have hs₂ := (le_abs_self (positiveScoreTerm y' - positiveScoreTerm (coordinateInf y y'))).trans
    (positiveScoreTerm_lipschitz_uniform hN y' (coordinateInf y y'))
  rw [← coordinateSup_sub_left y y'] at hs₂
  have hscaled := mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 11 / 32)
  have hp := progressReward_lattice_exchange y y'
  have hraw : coupledFunction y + coupledFunction y' - coupledFunction (coordinateInf y y') -
      coupledFunction (coordinateSup y y') =
      positiveScoreTerm y + positiveScoreTerm y' - positiveScoreTerm (coordinateInf y y') -
        positiveScoreTerm (coordinateSup y y') := by
    simp only [coupledFunction_eq_score_sub_reward]
    linarith
  dsimp [sourcePayoff] at hmin hmax hy hy'
  linarith

theorem chain_remote_sources_inner_gt {M N : ℕ} (hN : 256 ≤ N)
    {z y y' g g' : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 z)
    (hy' : y' ∈ majorantSources coupledFunction 2 z)
    (hzy : z ≠ y) (hzy' : z ≠ y')
    (hg : g ∈ subdifferential coupledFunction y)
    (hg' : g' ∈ subdifferential coupledFunction y')
    (hrr : ‖z - y‖ ≤ ‖z - y'‖) (hr8 : ‖z - y'‖ ≤ 8 * ‖z - y‖) :
    (1 / 8 : ℝ) < inner ℝ g g' := by
  by_contra h
  have hinner : inner ℝ g g' ≤ 1 / 8 := le_of_not_gt h
  have hNpos : 0 < N := by omega
  let d := z - y
  let d' := z - y'
  let r := ‖d‖
  let r' := ‖d'‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
  have hr' : 0 < r' := norm_pos_iff.mpr (sub_ne_zero.mpr hzy')
  have hgform := chain_remote_source_subgradient hNpos hy hzy hg
  have hgform' := chain_remote_source_subgradient hNpos hy' hzy' hg'
  rw [hgform, hgform', real_inner_smul_left, real_inner_smul_right] at hinner
  change (-2 / r) * ((-2 / r') * inner ℝ d d') ≤ 1 / 8 at hinner
  have hm := mul_le_mul_of_nonneg_left hinner (mul_nonneg hr.le hr'.le)
  have heq : r * r' * ((-2 / r) * ((-2 / r') * inner ℝ d d')) = 4 * inner ℝ d d' := by
    field_simp <;> ring
  rw [heq] at hm
  have hdot : inner ℝ d d' ≤ r * r' / 32 := by nlinarith
  have hcoord := chain_source_coord_le hNpos hy
  have hcoord' := chain_source_coord_le hNpos hy'
  have hd : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hcoord i)
  have hd' : ∀ i, 0 ≤ d' i := fun i => sub_nonneg.mpr (hcoord' i)
  have hsmall := (lattice_inf_sq_le_inner hd hd').trans hdot
  have horder := lattice_inf_norm_le_sup hd hd'
  have hidentity : ‖coordinateSup d d'‖ ^ 2 + ‖coordinateInf d d'‖ ^ 2 = r ^ 2 + r' ^ 2 := by
    have hi := lattice_norm_sq_add d d'
    change _ = ‖d‖ ^ 2 + ‖d'‖ ^ 2
    linarith
  let q := r' / r
  let u := ‖coordinateSup d d'‖ / r
  let v := ‖coordinateInf d d'‖ / r
  have hq0 : 1 ≤ q := (le_div_iff₀ hr).mpr (by simpa [r, r', d, d'] using hrr)
  have hq8 : q ≤ 8 := (div_le_iff₀ hr).mpr (by simpa [r, r', d, d', mul_comm] using hr8)
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hr.le
  have hv : 0 ≤ v := div_nonneg (norm_nonneg _) hr.le
  have hvu : v ≤ u := div_le_div_of_nonneg_right horder hr.le
  have hsq : u ^ 2 + v ^ 2 = 1 + q ^ 2 := by
    dsimp [u, v, q]
    field_simp
    nlinarith
  have hvs : v ^ 2 ≤ q / 32 := by
    calc
      v ^ 2 = ‖coordinateInf d d'‖ ^ 2 / r ^ 2 := by simp only [v, div_pow]
      _ ≤ (r * r' / 32) / r ^ 2 := div_le_div_of_nonneg_right hsmall (sq_nonneg r)
      _ = q / 32 := by dsimp [q]; field_simp
  have hcomp := chain_source_lattice_comparison hN hy hy'
  rw [upper_sub_coordinateInf, upper_sub_coordinateSup] at hcomp
  change r + r' - ‖coordinateSup d d'‖ - ‖coordinateInf d d'‖ ≤ (11 / 32 : ℝ) * r at hcomp
  have hcompnorm : 1 + q - u - v ≤ 11 / 32 := by
    calc
      _ = (r + r' - ‖coordinateSup d d'‖ - ‖coordinateInf d d'‖) / r := by
        dsimp [q, u, v]; field_simp
      _ ≤ ((11 / 32 : ℝ) * r) / r := div_le_div_of_nonneg_right hcomp hr.le
      _ = 11 / 32 := by field_simp
  exact (not_lt_of_ge hcompnorm) (source_band_normalized_contradiction hq0 hq8 hu hv hvu hsq hvs)

end WC
