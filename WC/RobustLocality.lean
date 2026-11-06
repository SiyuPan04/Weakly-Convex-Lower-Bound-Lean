import WC.ChainSources
import WC.RawBarrier
import WC.RobustParameters

/-!
# Every-source restrictions for robust full-oracle locality

The arguments concern actual maximizing sources of the least Lipschitz
majorant, rather than a selected subgradient or a restricted oracle.
-/

noncomputable section
namespace WC
open scoped BigOperators Classical

theorem active_coupled_branch_gradient_mem {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (y : ChainSpace M N)
    (hactive : coupledFacetBranch w a y = coupledFunction y) :
    coupledFacetBranchGradient w a y ∈ subdifferential coupledFunction y := by
  rw [subdifferential_coupledFunction_eq_convexHull hN]
  exact subset_convexHull ℝ _ ⟨w, hw, a, hactive, rfl⟩

theorem progressGradient_zero_of_hidden {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    (u : EuclideanSpace ℝ (Fin N)) (n : Fin N) (hn : u n ≤ robustTolerance M N) :
    progressGradient u n = 0 := by
  have hz := (hidden_progress_and_slope_zero hM hN hn).2
  change progressGateSlope _ / 4 = 0
  rw [hz]
  norm_num

theorem affineFacetGradient_coordinate (N : ℕ) (a : FanFacet N) (n : Fin N) :
    affineFacetGradient N a n = if a = some n then -(N : ℝ) / 8 else 0 := by
  cases a with
  | none => simp [affineFacetGradient]
  | some j => simp [affineFacetGradient, eq_comm]

/-- A hidden coordinate has no smooth progress derivative. Its entire
smooth facet-branch gradient is therefore the pure weighted fan slope. -/
theorem coupled_branch_gradient_hidden {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (a : Fin M → FanFacet N)
    (y : ChainSpace M N) (m : Fin M) (n : Fin N)
    (hn : y (m, n) ≤ robustTolerance M N) :
    coupledFacetBranchGradient w a y (m, n) = if a m = some n then -w m / 4 else 0 := by
  have hp := progressGradient_zero_of_hidden hM hN (euclideanBlock y m) n hn
  rw [coupledFacetBranchGradient_apply]
  simp only [blockFacetGradient, PiLp.add_apply, PiLp.smul_apply,
    smoothBlockGradient, hp, mul_zero, add_zero, smul_eq_mul,
    affineFacetGradient_coordinate]
  split_ifs
  · have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
    ring
  · ring

theorem source_hidden_progressGradient_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N) :
    progressGradient (euclideanBlock y m) n = 0 :=
  progressGradient_zero_of_hidden hM hN _ n ((chain_source_coord_le hN hy (m, n)).trans hn)

/-- At a remote source, a hidden displacement can occur only at the
single facet selected by any one attaining smooth branch. -/
theorem remote_source_hidden_unchanged_of_not_facet {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (hxy : x ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N)
    (hfacet : a m ≠ some n) : y (m, n) = x (m, n) := by
  have hgrad := active_coupled_branch_gradient_mem hN w hw a y hactive
  have hradial := chain_remote_source_subgradient hN hy hxy hgrad
  have hcoord := congrArg (fun v : ChainSpace M N => v (m, n)) hradial
  have hflat := coupled_branch_gradient_hidden hM hN w a y m n
    ((chain_source_coord_le hN hy (m, n)).trans hn)
  rw [if_neg hfacet] at hflat
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hcoord
  rw [hflat] at hcoord
  have hR : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hfactor : (-2 / ‖x - y‖ : ℝ) ≠ 0 := div_ne_zero (by norm_num) hR
  have hz := (mul_eq_zero.mp hcoord.symm).resolve_left hfactor
  linarith

/-- The manuscript's source equation for a moving hidden fan coordinate. -/
theorem remote_source_hidden_displacement {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (hxy : x ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N)
    (hfacet : a m = some n) : x (m, n) - y (m, n) = ‖x - y‖ * w m / 8 := by
  have hgrad := active_coupled_branch_gradient_mem hN w hw a y hactive
  have hradial := chain_remote_source_subgradient hN hy hxy hgrad
  have hcoord := congrArg (fun v : ChainSpace M N => v (m, n)) hradial
  have hflat := coupled_branch_gradient_hidden hM hN w a y m n
    ((chain_source_coord_le hN hy (m, n)).trans hn)
  rw [if_pos hfacet] at hflat
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hcoord
  rw [hflat] at hcoord
  have hR : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  field_simp at hcoord
  nlinarith [hcoord]

/-- Every source has at most one moving hidden coordinate in each block.
This restriction applies to every maximizing source, not an oracle selection. -/
theorem source_hidden_displacements_unique {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (m : Fin M) (n n' : Fin N)
    (hn : x (m, n) ≤ robustTolerance M N) (hn' : x (m, n') ≤ robustTolerance M N)
    (hmove : y (m, n) < x (m, n)) (hmove' : y (m, n') < x (m, n')) : n = n' := by
  have hxy : x ≠ y := by
    intro h
    rw [h] at hmove
    exact (lt_irrefl _ hmove)
  obtain ⟨w, hw, a, hactive⟩ := coupledFacetBranch_attains_coupledFunction y
  have hfacet : a m = some n := by
    by_contra hne
    have heq := remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive m n hn hne
    linarith
  have hfacet' : a m = some n' := by
    by_contra hne
    have heq := remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive m n' hn' hne
    linarith
  exact Option.some.inj (hfacet.symm.trans hfacet')

section SwapDisplacement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transfer a displacement by swapping its coordinate labels. This
preserves its Euclidean norm exactly, even for a nonzero hidden query. -/
def swappedDisplacementSource (x y : EuclideanSpace ℝ ι) (i j : ι) : EuclideanSpace ℝ ι :=
  x - LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) (x - y)

theorem swappedDisplacementSource_distance (x y : EuclideanSpace ℝ ι) (i j : ι) :
    ‖x - swappedDisplacementSource x y i j‖ = ‖x - y‖ := by
  rw [swappedDisplacementSource, sub_sub_cancel]
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)).norm_map (x - y)

theorem swappedDisplacementSource_apply (x y : EuclideanSpace ℝ ι) (i j k : ι) :
    swappedDisplacementSource x y i j k = x k - (x (Equiv.swap i j k) - y (Equiv.swap i j k)) := by
  simp [swappedDisplacementSource, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem swappedDisplacementSource_left (x y : EuclideanSpace ℝ ι) (i j : ι) :
    swappedDisplacementSource x y i j i = x i - (x j - y j) := by
  rw [swappedDisplacementSource_apply]
  simp

theorem swappedDisplacementSource_right (x y : EuclideanSpace ℝ ι) (i j : ι) :
    swappedDisplacementSource x y i j j = x j - (x i - y i) := by
  rw [swappedDisplacementSource_apply]
  simp

theorem swappedDisplacementSource_other (x y : EuclideanSpace ℝ ι) (i j k : ι)
    (hki : k ≠ i) (hkj : k ≠ j) : swappedDisplacementSource x y i j k = y k := by
  rw [swappedDisplacementSource_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  ring

theorem swappedDisplacementSource_coord_le {x y : EuclideanSpace ℝ ι}
    (hle : ∀ k, y k ≤ x k) (i j k : ι) : swappedDisplacementSource x y i j k ≤ x k := by
  rw [swappedDisplacementSource_apply]
  have h := hle (Equiv.swap i j k)
  linarith

end SwapDisplacement

theorem swappedDisplacementSource_progress_term {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hle : ∀ k, y k ≤ x k) (i j k : Fin M × Fin N)
    (hi : x i ≤ robustTolerance M N) (hj : x j ≤ robustTolerance M N) :
    progressGate ((N : ℝ) / 4 * swappedDisplacementSource x y i j k - 1 / (64 * (N : ℝ))) =
      progressGate ((N : ℝ) / 4 * y k - 1 / (64 * (N : ℝ))) := by
  by_cases hki : k = i
  · subst k
    have hnew := (hidden_progress_and_slope_zero hM hN
      ((swappedDisplacementSource_coord_le hle i j i).trans hi)).1
    have hold := (hidden_progress_and_slope_zero hM hN ((hle i).trans hi)).1
    rw [hnew, hold]
  · by_cases hkj : k = j
    · subst k
      have hnew := (hidden_progress_and_slope_zero hM hN
        ((swappedDisplacementSource_coord_le hle i j j).trans hj)).1
      have hold := (hidden_progress_and_slope_zero hM hN ((hle j).trans hj)).1
      rw [hnew, hold]
    · rw [swappedDisplacementSource_other x y i j k hki hkj]

theorem swappedDisplacementSource_progress {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hle : ∀ k, y k ≤ x k) (i j : Fin M × Fin N)
    (hi : x i ≤ robustTolerance M N) (hj : x j ≤ robustTolerance M N) (m : Fin M) :
    blockProgress (coupledBlock (swappedDisplacementSource x y i j) m) =
      blockProgress (coupledBlock y m) := by
  unfold blockProgress
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact swappedDisplacementSource_progress_term hM hN hle i j (m, n) hi hj

theorem swappedDisplacementSource_gate {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hle : ∀ k, y k ≤ x k) (i j : Fin M × Fin N)
    (hi : x i ≤ robustTolerance M N) (hj : x j ≤ robustTolerance M N) (m : Fin M) :
    precedingGate (swappedDisplacementSource x y i j) m = precedingGate y m := by
  unfold precedingGate
  split_ifs
  · rfl
  · rw [swappedDisplacementSource_progress hM hN hle i j hi hj]

theorem swappedDisplacementSource_block_other {M N : ℕ} (x y : ChainSpace M N)
    (i j : Fin M × Fin N) (m : Fin M) (hmi : m ≠ i.1) (hmj : m ≠ j.1) :
    coupledBlock (swappedDisplacementSource x y i j) m = coupledBlock y m := by
  funext n
  apply swappedDisplacementSource_other x y i j (m, n)
  · exact fun h => hmi (congrArg Prod.fst h)
  · exact fun h => hmj (congrArg Prod.fst h)

theorem swappedDisplacementSource_score_other {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hle : ∀ k, y k ≤ x k) (i j : Fin M × Fin N)
    (hi : x i ≤ robustTolerance M N) (hj : x j ≤ robustTolerance M N)
    (m : Fin M) (hmi : m ≠ i.1) (hmj : m ≠ j.1) :
    coupledScore (swappedDisplacementSource x y i j) m = coupledScore y m := by
  unfold coupledScore
  rw [swappedDisplacementSource_block_other x y i j m hmi hmj,
    swappedDisplacementSource_gate hM hN hle i j hi hj m]

/-- A strict increase of an already positive score strictly increases
the positive-score Euclidean norm. -/
theorem positive_score_norm_strict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : EuclideanSpace ℝ ι) (i : ι) (hpos : 0 < s i) (hinc : s i < t i)
    (hsame : ∀ j, j ≠ i → t j = s j) : ‖positiveScores s‖ < ‖positiveScores t‖ := by
  have hsq : ‖positiveScores s‖ ^ 2 < ‖positiveScores t‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hji : j = i
      · subst j
        change (max (s i) 0) ^ 2 ≤ (max (t i) 0) ^ 2
        rw [max_eq_left hpos.le, max_eq_left (hpos.trans hinc).le]
        nlinarith
      · rw [show positiveScores t j = positiveScores s j by simp [positiveScores, hsame j hji]]
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      change (max (s i) 0) ^ 2 < (max (t i) 0) ^ 2
      rw [max_eq_left hpos.le, max_eq_left (hpos.trans hinc).le]
      nlinarith
  nlinarith [norm_nonneg (positiveScores s), norm_nonneg (positiveScores t)]

theorem robustTolerance_le_inv_N (M : ℕ) {N : ℕ} (hN : 0 < N) :
    robustTolerance M N ≤ 1 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold robustTolerance
  apply one_div_le_one_div_of_le hn
  have hK : (0 : ℝ) ≤ (M * N : ℕ) := Nat.cast_nonneg _
  nlinarith

theorem hidden_fanPiece_gt_quarter {M N : ℕ} (hN : 0 < N)
    (y : ChainSpace M N) (m : Fin M) (n : Fin N)
    (hn : y (m, n) ≤ robustTolerance M N) :
    1 / 4 < fanPiece N (M * N) m.val (coupledBlock y m) n := by
  have hrank : m.val * N + n.val < M * N := by
    calc
      _ < m.val * N + N := Nat.add_lt_add_left n.isLt _
      _ = (m.val + 1) * N := by ring
      _ ≤ M * N := Nat.mul_le_mul_right N m.isLt
  have hc := tiltIntercept_gt_one hrank
  have hm := mul_le_mul_of_nonneg_left (hn.trans (robustTolerance_le_inv_N M hN))
    (show (0 : ℝ) ≤ (N : ℝ) / 8 by positivity)
  have heq : (N : ℝ) / 8 * (1 / (N : ℝ)) = 1 / 8 := by field_simp
  rw [heq] at hm
  dsimp only [fanPiece, coupledBlock]
  linarith

theorem source_positive_score_norm_of_hidden {M N : ℕ} (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N) :
    0 < ‖positiveCoupledScores y‖ := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro hz
  have hterm := (positiveCoupledScores_norm_eq_zero_iff_terminalRegion hN y).mp hz.symm
  have hf := hidden_fanPiece_gt_quarter hN y m n ((chain_source_coord_le hN hy (m, n)).trans hn)
  exact (not_le_of_gt hf) (hterm m n)

theorem source_active_weight_score_pos {M N : ℕ} (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N) (hwm : 0 < w m) :
    0 < coupledScore y m := by
  have hR := source_positive_score_norm_of_hidden hN hy m n hn
  have heq := activeFacet_weight_eq_optimizer hN y hR w hw a hactive
  have hopt : 0 < positiveScoreOptimizer (coupledScores y) m := by rw [← heq]; exact hwm
  exact (positiveScoreOptimizer_pos_iff (coupledScores y) hR m).mp hopt

/-- An attaining, positively weighted branch of any maximizing source
cannot select a later hidden facet. Swapping displacements strictly
raises its positive block score without changing progress or distance. -/
theorem source_no_later_hidden_active_facet {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (k n : Fin N) (hkn : k.val < n.val)
    (hk : |x (m, k)| ≤ robustTolerance M N) (hn : |x (m, n)| ≤ robustTolerance M N)
    (hwm : 0 < w m) : a m ≠ some n := by
  intro hfacet
  have hle := chain_source_coord_le hN hy
  have hkupper := (abs_le.mp hk).2
  have hnupper := (abs_le.mp hn).2
  let y' := swappedDisplacementSource x y (m, k) (m, n)
  have hgap := activeFacet_weighted_gap_zero hN w hw a y hactive m
  have hfanEq := sub_eq_zero.mp ((mul_eq_zero.mp hgap).resolve_left (ne_of_gt hwm))
  have hfan : tiltedBlock N (M * N) m.val (coupledBlock y m) =
      fanPiece N (M * N) m.val (coupledBlock y m) n := by
    calc
      _ = euclideanTiltedBlock N (M * N) m.val (euclideanBlock y m) := rfl
      _ = affineFacet N (M * N) m.val (a m) (euclideanBlock y m) := hfanEq
      _ = fanPiece N (M * N) m.val (coupledBlock y m) n := by rw [hfacet]; rfl
  have horder := robust_tilt_order_strict hN (Nat.add_lt_add_left hkn (m.val * N)) hk hn
  have hpiece : fanPiece N (M * N) m.val (coupledBlock y m) n <
      fanPiece N (M * N) m.val (coupledBlock y' m) k := by
    dsimp only [y', fanPiece, coupledBlock]
    rw [swappedDisplacementSource_left]
    nlinarith [horder]
  have hfangain : tiltedBlock N (M * N) m.val (coupledBlock y m) <
      tiltedBlock N (M * N) m.val (coupledBlock y' m) := by
    rw [hfan]
    exact hpiece.trans_le (fanPiece_le_tiltedBlock N (M * N) m.val (coupledBlock y' m) k)
  have hscore : 0 < coupledScore y m := source_active_weight_score_pos hN hy w hw a hactive m n hnupper hwm
  have hscoregain : coupledScore y m < coupledScore y' m := by
    unfold coupledScore
    dsimp only [y']
    rw [swappedDisplacementSource_gate hM hN hle (m, k) (m, n) hkupper hnupper]
    linarith [hfangain]
  have hsamescore (j : Fin M) (hjm : j ≠ m) : coupledScore y' j = coupledScore y j :=
    swappedDisplacementSource_score_other hM hN hle (m, k) (m, n) hkupper hnupper j hjm hjm
  have hnormgain := positive_score_norm_strict (coupledScores y) (coupledScores y') m hscore hscoregain hsamescore
  change ‖positiveCoupledScores y‖ < ‖positiveCoupledScores y'‖ at hnormgain
  have hprogress : (∑ j, blockProgress (coupledBlock y' j)) = ∑ j, blockProgress (coupledBlock y j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact swappedDisplacementSource_progress hM hN hle (m, k) (m, n) hkupper hnupper j
  have hf : coupledFunction y < coupledFunction y' := by
    unfold coupledFunction
    rw [hprogress]
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hnormgain _) (by positivity)
  have hdistance : ‖x - y'‖ = ‖x - y‖ := swappedDisplacementSource_distance x y (m, k) (m, n)
  have hpayoff : sourcePayoff coupledFunction 2 x y < sourcePayoff coupledFunction 2 x y' := by
    unfold sourcePayoff
    rw [hdistance]
    linarith
  have hupper := payoff_le_majorant (chainMajorant_finite hN) x y'
  change sourcePayoff coupledFunction 2 x y = lipschitzMajorant coupledFunction 2 x at hy
  linarith

/-- Every actual raw source subgradient vanishes on every hidden
coordinate later than another hidden coordinate in its block. -/
theorem source_subgradient_hidden_later_zero {M N : ℕ}
    (hM : 1 ≤ M) (hN : 0 < N) {x y v : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x)
    (hv : v ∈ subdifferential coupledFunction y)
    (m : Fin M) (k n : Fin N) (hkn : k.val < n.val)
    (hk : |x (m, k)| ≤ robustTolerance M N) (hn : |x (m, n)| ≤ robustTolerance M N) :
    v (m, n) = 0 := by
  rw [subdifferential_coupledFunction_eq_convexHull hN] at hv
  have hconv : Convex ℝ {g : ChainSpace M N | g (m, n) = 0} := by
    intro g hg h hh s t _ _ _
    change s * g (m, n) + t * h (m, n) = 0
    simp only [Set.mem_setOf_eq] at hg hh
    simp [hg, hh]
  have hgenerators : coupledActiveGradients y ⊆ {g : ChainSpace M N | g (m, n) = 0} := by
    rintro g ⟨w, hw, a, hactive, rfl⟩
    change coupledFacetBranchGradient w a y (m, n) = 0
    have hhidden := coupled_branch_gradient_hidden hM hN w a y m n
      ((chain_source_coord_le hN hy (m, n)).trans (abs_le.mp hn).2)
    by_cases hzero : w m = 0
    · rw [hhidden]
      split_ifs <;> simp [hzero]
    · have hwm : 0 < w m := lt_of_le_of_ne (hw.1 m) (Ne.symm hzero)
      rw [hhidden, if_neg (source_no_later_hidden_active_facet hM hN hy w hw a hactive m k n hkn hk hn hwm)]
  exact convexHull_min hgenerators hconv hv

/-- The full majorant subdifferential inherits the same source restriction. -/
theorem chainMajorant_subgradient_hidden_later_zero {M N : ℕ}
    (hM : 1 ≤ M) (hN : 256 ≤ N) {x v : ChainSpace M N}
    (hv : v ∈ subdifferential chainMajorant x)
    (m : Fin M) (k n : Fin N) (hkn : k.val < n.val)
    (hk : |x (m, k)| ≤ robustTolerance M N) (hn : |x (m, n)| ≤ robustTolerance M N) :
    v (m, n) = 0 := by
  rw [chainMajorant_subdifferential hN] at hv
  have hconv : Convex ℝ {g : ChainSpace M N | g (m, n) = 0} := by
    intro g hg h hh s t _ _ _
    change s * g (m, n) + t * h (m, n) = 0
    simp only [Set.mem_setOf_eq] at hg hh
    simp [hg, hh]
  have hslopes : sourceSlopes coupledFunction 2 x ⊆ {g : ChainSpace M N | g (m, n) = 0} := by
    rintro g ⟨y, hy, hg⟩
    exact source_subgradient_hidden_later_zero hM (by omega) hy hg m k n hkn hk hn
  exact convexHull_min hslopes hconv hv

section SuffixConcentration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem euclidean_norm_strict_mono_nonneg (u v : EuclideanSpace ℝ ι)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (hle : ∀ i, u i ≤ v i)
    (hstrict : ∃ i, u i < v i) : ‖u‖ < ‖v‖ := by
  have hs : ‖u‖ ^ 2 < ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_lt_sum
    · intro i _
      exact (sq_le_sq₀ (hu i) (hv i)).mpr (hle i)
    · obtain ⟨i, hi⟩ := hstrict
      exact ⟨i, Finset.mem_univ _, by nlinarith [hu i, hv i]⟩
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Concentrating a nonnegative suffix displacement in the block with
strictly largest baseline strictly raises its positive-score norm whenever
a later block moves. This is the finite-dimensional comparison behind
manuscript lines 2156--2172. -/
theorem suffix_concentration_strict (b r : EuclideanSpace ℝ ι) (i : ι)
    {a : ℝ} (ha : 0 < a) (hr : ∀ j, 0 ≤ r j)
    (horder : ∀ j, j ≠ i → b j < b i) (hnegative : ∀ j, j ≠ i → b j < 0)
    (hmoving : ∃ j, j ≠ i ∧ 0 < r j)
    (hpositive : 0 < ‖positiveScores (b + a • r)‖) :
    ‖positiveScores (b + a • r)‖ < b i + a * ‖r‖ := by
  let v := positiveScores (b + a • r)
  let S := ‖v‖
  have hS : 0 < S := hpositive
  have hv (j : ι) : 0 ≤ v j := le_max_right _ _
  have hvnorm (j : ι) : v j ≤ S := by
    have hn := PiLp.norm_apply_le v j
    rwa [Real.norm_eq_abs, abs_of_nonneg (hv j)] at hn
  obtain ⟨j₀, hj₀, hmove⟩ := hmoving
  by_cases hbi : 0 ≤ b i
  · let u := a • r + EuclideanSpace.single i (b i)
    have hu (j : ι) : 0 ≤ u j := by
      change 0 ≤ a * r j + EuclideanSpace.single i (b i) j
      have hs : 0 ≤ EuclideanSpace.single i (b i) j := by
        by_cases hji : j = i
        · subst j; simpa using hbi
        · simp [hji]
      exact add_nonneg (mul_nonneg ha.le (hr j)) hs
    have hle (j : ι) : v j ≤ u j := by
      by_cases hji : j = i
      · subst j
        change max (b i + a * r i) 0 ≤ a * r i + EuclideanSpace.single i (b i) i
        rw [show EuclideanSpace.single i (b i) i = b i by simp]
        rw [max_eq_left (add_nonneg hbi (mul_nonneg ha.le (hr i)))]
        linarith
      · change max (b j + a * r j) 0 ≤ a * r j + EuclideanSpace.single i (b i) j
        simp only [PiLp.single_apply, if_neg hji, add_zero]
        exact max_le (by linarith [hnegative j hji]) (mul_nonneg ha.le (hr j))
    have hstrict : v j₀ < u j₀ := by
      change max (b j₀ + a * r j₀) 0 < a * r j₀ + EuclideanSpace.single i (b i) j₀
      simp only [PiLp.single_apply, if_neg hj₀, add_zero]
      exact max_lt (by linarith [hnegative j₀ hj₀]) (mul_pos ha hmove)
    have hnorm := euclidean_norm_strict_mono_nonneg v u hv hu hle ⟨j₀, hstrict⟩
    have htri : ‖u‖ ≤ a * ‖r‖ + b i := by
      calc
        ‖u‖ ≤ ‖a • r‖ + ‖EuclideanSpace.single i (b i)‖ := norm_add_le _ _
        _ = a * ‖r‖ + b i := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, PiLp.norm_single,
            Real.norm_eq_abs, abs_of_nonneg hbi]
    exact hnorm.trans_le (by simpa only [add_comm] using htri)
  · let c := -b i
    have hc : 0 < c := by dsimp [c]; linarith
    let q := (1 + c / S) • v
    have hcoef : 0 < 1 + c / S := by positivity
    have hq (j : ι) : 0 ≤ q j := mul_nonneg hcoef.le (hv j)
    have har (j : ι) : 0 ≤ (a • r) j := mul_nonneg ha.le (hr j)
    have hbase (j : ι) : b j ≤ b i := by
      by_cases hji : j = i
      · subst j; rfl
      · exact (horder j hji).le
    have hmult (j : ι) : (c / S) * v j ≤ c := by
      have hm := mul_le_mul_of_nonneg_left (hvnorm j) (show 0 ≤ c / S by positivity)
      rwa [div_mul_cancel₀ c hS.ne'] at hm
    have hle (j : ι) : q j ≤ (a • r) j := by
      change (1 + c / S) * v j ≤ a * r j
      by_cases hp : 0 ≤ b j + a * r j
      · have heq : v j = b j + a * r j := max_eq_left hp
        have hb := hbase j
        dsimp only [c] at hmult ⊢
        nlinarith [hmult j, heq]
      · have heq : v j = 0 := max_eq_right (le_of_not_ge hp)
        rw [heq, mul_zero]
        exact mul_nonneg ha.le (hr j)
    have hstrict : q j₀ < (a • r) j₀ := by
      change (1 + c / S) * v j₀ < a * r j₀
      by_cases hp : 0 ≤ b j₀ + a * r j₀
      · have heq : v j₀ = b j₀ + a * r j₀ := max_eq_left hp
        have hb := horder j₀ hj₀
        have hm := hmult j₀
        dsimp only [c] at hm ⊢
        nlinarith [heq]
      · have heq : v j₀ = 0 := max_eq_right (le_of_not_ge hp)
        rw [heq, mul_zero]
        exact mul_pos ha hmove
    have hnorm := euclidean_norm_strict_mono_nonneg q (a • r) hq har hle ⟨j₀, hstrict⟩
    have hnq : ‖q‖ = S + c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
      change (1 + c / S) * S = S + c
      field_simp
    rw [hnq, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
    dsimp only [c, S] at hnorm
    linarith

end SuffixConcentration

end WC
