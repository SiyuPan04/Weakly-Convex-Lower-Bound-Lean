import WC.SaturatedSubgradient
import WC.MonotoneSubgradient
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual active-score stationarity barrier for the raw coupled function. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem positiveScoreOptimizer_norm_eq_one {ι : Type*} [Fintype ι]
    (s : EuclideanSpace ℝ ι) (hs : 0 < ‖positiveScores s‖) : ‖positiveScoreOptimizer s‖ = 1 := by
  have hp : positiveScores s ≠ 0 := norm_pos_iff.mp hs
  simp [positiveScoreOptimizer, hp, norm_smul, hs.ne']

theorem positiveScoreOptimizer_unique {ι : Type*} [Fintype ι]
    (s : EuclideanSpace ℝ ι) (hs : 0 < ‖positiveScores s‖)
    (w : EuclideanSpace ℝ ι) (hw : w ∈ scoreWeights) (hattain : inner ℝ w s = ‖positiveScores s‖) :
    w = positiveScoreOptimizer s := by
  have hp : positiveScores s ≠ 0 := norm_pos_iff.mp hs
  have hinner : inner ℝ w s ≤ inner ℝ w (positiveScores s) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1 i)
  have hnorm := positiveScoreOptimizer_norm_eq_one s hs
  have hoptinner : 1 ≤ inner ℝ w (positiveScoreOptimizer s) := by
    unfold positiveScoreOptimizer
    rw [if_neg hp, real_inner_smul_right]
    have h := mul_le_mul_of_nonneg_left hinner (le_of_lt (inv_pos.mpr hs))
    rw [hattain, inv_mul_cancel₀ hs.ne'] at h
    exact h
  have hwsq : ‖w‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg w) (show (0 : ℝ) ≤ 1 by norm_num)).mpr hw.2
  have hd := norm_sub_sq_real w (positiveScoreOptimizer s)
  have hzero : ‖w - positiveScoreOptimizer s‖ = 0 := by
    rw [hnorm] at hd
    nlinarith [norm_nonneg (w - positiveScoreOptimizer s)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem activeFacet_weight_eq_optimizer {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (hactive : coupledFacetBranch w a x = coupledFunction x) :
    w = positiveScoreOptimizer (coupledScores x) := by
  have hvalue : weightedCoupledFunction w x = coupledFunction x := le_antisymm
    (weightedCoupledFunction_le w x hw)
    (hactive.symm.le.trans (coupledFacetBranch_le_weightedCoupledFunction w hw a x))
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  change (2 / (N : ℝ)) * (inner ℝ w (coupledScores x) - 2 * ∑ m, blockProgress (coupledBlock x m)) =
    (2 / (N : ℝ)) * (‖positiveCoupledScores x‖ - 2 * ∑ m, blockProgress (coupledBlock x m)) at hvalue
  have heq := mul_left_cancel₀ (ne_of_gt (by positivity : 0 < 2 / (N : ℝ))) hvalue
  have hinner : inner ℝ w (coupledScores x) = ‖positiveScores (coupledScores x)‖ := by
    change inner ℝ w (coupledScores x) = ‖positiveCoupledScores x‖
    linarith
  exact positiveScoreOptimizer_unique (coupledScores x) hR w hw hinner

theorem positiveScoreOptimizer_pos_iff {ι : Type*} [Fintype ι]
    (s : EuclideanSpace ℝ ι) (hs : 0 < ‖positiveScores s‖) (i : ι) :
    0 < positiveScoreOptimizer s i ↔ 0 < s i := by
  have hp : positiveScores s ≠ 0 := norm_pos_iff.mp hs
  unfold positiveScoreOptimizer
  rw [if_neg hp]
  change 0 < ‖positiveScores s‖⁻¹ * max (s i) 0 ↔ 0 < s i
  rw [mul_pos_iff_of_pos_left (inv_pos.mpr hs)]
  simp

theorem affineFacetGradient_sum (N : ℕ) (a : FanFacet N) :
    (∑ n, affineFacetGradient N a n) = if a = none then 0 else -(N : ℝ) / 8 := by
  cases a with
  | none => simp [affineFacetGradient]
  | some n => simp [affineFacetGradient]

theorem smoothBlockGradient_coordinate_nonpos {N : ℕ} {ω : ℝ} (_hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (x : EuclideanSpace ℝ (Fin N)) (n : Fin N) : smoothBlockGradient ω x n ≤ 0 := by
  have hnonneg := relaySlope_nonneg (euclideanProgress x)
  have hle := relaySlope_le (euclideanProgress x)
  have hω := mul_le_mul_of_nonneg_right hω1 hnonneg
  have hc : ω * relaySlope (euclideanProgress x) - 2 ≤ 0 := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg hc (progressGradient_nonneg x n)

theorem activeFacetBranchGradient_block_sum_le {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (hactive : coupledFacetBranch w a x = coupledFunction x) (m : Fin M) :
    (∑ n, coupledFacetBranchGradient w a x (m, n)) ≤ -(w m) / 4 := by
  have hweight := activeFacet_weight_eq_optimizer hN x hR w hw a hactive
  have hfan : (∑ n, w m * affineFacetGradient N (a m) n) = -(w m) * (N : ℝ) / 8 := by
    rw [← Finset.mul_sum, affineFacetGradient_sum]
    by_cases hwzero : w m = 0
    · simp [hwzero]
    have hwpos : 0 < w m := lt_of_le_of_ne (hw.1 m) (Ne.symm hwzero)
    have hscore : 0 < coupledScore x m := by
      have h := (positiveScoreOptimizer_pos_iff (coupledScores x) hR m).mp
        (by simpa only [← hweight] using hwpos)
      exact h
    have hphi : 1 / 4 < euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) := by
      change 1 / 4 < tiltedBlock N (M * N) m.val (coupledBlock x m)
      have hg := precedingGate_le_one x m
      unfold coupledScore at hscore
      linarith
    have hgap := activeFacet_weighted_gap_zero hN w hw a x hactive m
    have hfaceteq : affineFacet N (M * N) m.val (a m) (euclideanBlock x m) =
        euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) := by
      have hdiff := (mul_eq_zero.mp hgap).resolve_left hwzero
      linarith
    have ha : a m ≠ none := by
      intro hn
      rw [hn] at hfaceteq
      change 0 = euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) at hfaceteq
      linarith
    rw [if_neg ha]
    ring
  have hsmooth : (∑ n, smoothBlockGradient (nextWeight w m) (euclideanBlock x m) n) ≤ 0 :=
    Finset.sum_nonpos fun n _ => smoothBlockGradient_coordinate_nonpos
      (nextWeight_nonneg hw m) (nextWeight_le_one hw m) _ n
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Finset.mul_sum] at hfan
  simp only [coupledFacetBranchGradient_apply, ← Finset.mul_sum, blockFacetGradient,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [hfan]
  have h := mul_le_mul_of_nonneg_left hsmooth (show 0 ≤ 2 / (N : ℝ) by positivity)
  have hid : (2 / (N : ℝ)) * (-(w m) * (N : ℝ) / 8) = -(w m) / 4 := by field_simp; ring
  nlinarith

theorem coupledFunction_subgradient_block_sum_le {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    {v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x) (m : Fin M) :
    (∑ n, v (m, n)) ≤ -(positiveScoreOptimizer (coupledScores x) m) / 4 := by
  rw [subdifferential_coupledFunction_eq_convexHull hN] at hv
  let w := positiveScoreOptimizer (coupledScores x)
  have hconv : Convex ℝ {g : ChainSpace M N | (∑ n, g (m, n)) ≤ -(w m) / 4} := by
    intro g hg h hh a b ha hb hab
    change (∑ n, g (m, n)) ≤ -(w m) / 4 at hg
    change (∑ n, h (m, n)) ≤ -(w m) / 4 at hh
    change (∑ n, (a • g + b • h) (m, n)) ≤ -(w m) / 4
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hga := mul_le_mul_of_nonneg_left hg ha
    have hhb := mul_le_mul_of_nonneg_left hh hb
    have hc : a * (-(w m) / 4) + b * (-(w m) / 4) = -(w m) / 4 := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hsub : coupledActiveGradients x ⊆ {g : ChainSpace M N | (∑ n, g (m, n)) ≤ -(w m) / 4} := by
    rintro g ⟨u, hu, a, hactive, rfl⟩
    have hueq := activeFacet_weight_eq_optimizer hN x hR u hu a hactive
    change (∑ n, coupledFacetBranchGradient u a x (m, n)) ≤ -(w m) / 4
    dsimp [w]
    rw [← hueq]
    exact activeFacetBranchGradient_block_sum_le hN x hR u hu a hactive m
  exact (convexHull_min hsub hconv) hv

theorem coupledFunction_subgradient_norm_sq_barrier {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    {v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x) :
    1 / (16 * (N : ℝ)) ≤ ‖v‖ ^ 2 := by
  let w := positiveScoreOptimizer (coupledScores x)
  have hw : w ∈ scoreWeights := positiveScoreOptimizer_mem _
  have hwnorm : ‖w‖ = 1 := positiveScoreOptimizer_norm_eq_one (coupledScores x) hR
  have hblock (m : Fin M) : (w m) ^ 2 / 16 ≤ (N : ℝ) * ∑ n, v (m, n) ^ 2 := by
    have hs := coupledFunction_subgradient_block_sum_le hN x hR hv m
    change (∑ n, v (m, n)) ≤ -(w m) / 4 at hs
    have hnonneg : 0 ≤ -(∑ n, v (m, n)) := by have h := hw.1 m; linarith
    have hsquare := (sq_le_sq₀ (div_nonneg (hw.1 m) (by norm_num : (0 : ℝ) ≤ 4)) hnonneg).mpr (by linarith)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ)) (fun n => v (m, n))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hc
    nlinarith
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hblock m)
  have hwsq : (∑ m, w m ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hwnorm]
    norm_num
  have hvsq : (∑ m : Fin M, ∑ n : Fin N, v (m, n) ^ 2) = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact (Fintype.sum_prod_type (fun i : Fin M × Fin N => v i ^ 2)).symm
  rw [← Finset.sum_div, ← Finset.mul_sum, hwsq, hvsq] at hsum
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (by positivity : 0 < 16 * (N : ℝ))).mpr
  nlinarith

/-- The actual full-subdifferential active-score barrier from Lemma `lem:active-subgradient-barrier`. -/
theorem coupledFunction_subgradient_norm_barrier {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    {v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x) :
    1 / (4 * Real.sqrt (N : ℝ)) ≤ ‖v‖ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hpos
  have hsq := coupledFunction_subgradient_norm_sq_barrier hN x hR hv
  have hid : (1 / (4 * Real.sqrt (N : ℝ))) ^ 2 = 1 / (16 * (N : ℝ)) := by
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)]
  apply (sq_le_sq₀ (by positivity) (norm_nonneg v)).mp
  rw [hid]
  exact hsq

theorem coupledFunction_active_subgradient_barrier {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hR : 0 < ‖positiveCoupledScores x‖)
    {v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x) :
    (∀ i, v i ≤ 0) ∧ 1 / (4 * Real.sqrt (N : ℝ)) ≤ ‖v‖ :=
  ⟨coupledFunction_subgradient_nonpos hN hv, coupledFunction_subgradient_norm_barrier hN x hR hv⟩

end WC
