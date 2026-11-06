import WC.RobustLocality
import WC.RemoteFanEquation
import WC.LocalityPerturbation
import WC.FrontGeometry

/-!
# Adjacent-front exclusion for every majorant source

The two-coordinate argument is independent of all later blocks: their
scores contribute fixed terms to the global score radius and their
coordinates contribute fixed terms to the source distance.
-/

noncomputable section
namespace WC
open scoped BigOperators Classical
open Filter Topology

def progressThreshold (N : ℕ) : ℝ := 1 / (16 * (N : ℝ) ^ 2)

theorem robustTolerance_lt_progressThreshold {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N) :
    robustTolerance M N < progressThreshold N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : (N : ℝ) ≤ (M * N : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left N hM
  unfold robustTolerance progressThreshold
  apply one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 16 * (N : ℝ) ^ 2)
  nlinarith

theorem progress_term_zero_of_le_threshold {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : u ≤ progressThreshold N) :
    progressGate ((N : ℝ) / 4 * u - 1 / (64 * (N : ℝ))) = 0 ∧
      progressGateSlope ((N : ℝ) / 4 * u - 1 / (64 * (N : ℝ))) = 0 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (N : ℝ) / 4 * progressThreshold N = 1 / (64 * (N : ℝ)) := by
    unfold progressThreshold
    field_simp
    norm_num
  have hm := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ (N : ℝ) / 4 by positivity)
  have harg : (N : ℝ) / 4 * u - 1 / (64 * (N : ℝ)) ≤ 0 := by rw [heq] at hm; linarith
  refine ⟨progressGate_of_nonpos harg, ?_⟩
  rw [progressGateSlope, if_pos harg]

theorem progressGradient_zero_of_le_threshold {N : ℕ} (hN : 0 < N)
    (u : EuclideanSpace ℝ (Fin N)) (n : Fin N) (hn : u n ≤ progressThreshold N) :
    progressGradient u n = 0 := by
  change progressGateSlope _ / 4 = 0
  rw [(progress_term_zero_of_le_threshold hN hn).2]
  norm_num

/-- At most a quarter of potentially nonflat coordinates cannot open
the next gate. This applies to source coordinates bounded by a hidden query. -/
theorem blockProgress_le_quarter_of_hidden {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    (u : Fin N → ℝ) (I : Finset (Fin N)) (hcard : 4 * I.card ≤ N)
    (hidden : ∀ n, n ∉ I → u n ≤ robustTolerance M N) : blockProgress u ≤ 1 / 4 := by
  let q : Fin N → ℝ := fun n => progressGate ((N : ℝ) / 4 * u n - 1 / (64 * (N : ℝ)))
  have hzero (n : Fin N) (hn : n ∉ I) : q n = 0 :=
    (hidden_progress_and_slope_zero hM hN (hidden n hn)).1
  have heq : (∑ n, q n) = ∑ n ∈ I, q n :=
    (Finset.sum_subset (Finset.subset_univ I) (fun n _ hn => hzero n hn)).symm
  have hsum : ∑ n, q n ≤ (I.card : ℝ) := by
    rw [heq]
    calc
      (∑ n ∈ I, q n) ≤ ∑ _n ∈ I, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => progressGate_le_one _)
      _ = I.card := by simp
  have hcardreal : 4 * (I.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  change (∑ n, q n) / (N : ℝ) ≤ 1 / 4
  apply (div_le_iff₀ hn).mpr
  linarith

theorem nextGate_zero_of_front_progress {M N : ℕ} (y : ChainSpace M N)
    (front next : Fin M) (hnext : next.val = front.val + 1)
    (hprogress : blockProgress (coupledBlock y front) ≤ 1 / 4) : precedingGate y next = 0 := by
  have hn0 : next.val ≠ 0 := by omega
  unfold precedingGate
  rw [if_neg hn0]
  have hprev : (⟨next.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) next.isLt⟩ : Fin M) = front := by
    apply Fin.ext
    change next.val - 1 = front.val
    omega
  rw [hprev]
  apply progressGate_of_nonpos
  linarith

theorem active_branch_weighted_score {M N : ℕ} (hN : 0 < N) (y : ChainSpace M N)
    (hR : 0 < ‖positiveCoupledScores y‖)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) : ‖positiveCoupledScores y‖ * w m = max (coupledScore y m) 0 := by
  have heq := activeFacet_weight_eq_optimizer hN y hR w hw a hactive
  have hP : positiveScores (coupledScores y) ≠ 0 := norm_pos_iff.mp hR
  rw [heq]
  unfold positiveScoreOptimizer
  rw [if_neg hP]
  change ‖positiveCoupledScores y‖ * (‖positiveCoupledScores y‖⁻¹ * max (coupledScore y m) 0) = _
  rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

theorem hidden_query_fan_baseline_neg {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (m : Fin M) (n : Fin N)
    (hn : |x (m, n)| ≤ robustTolerance M N) :
    tiltIntercept (M * N) (m.val * N + n.val) - (N : ℝ) / 8 * x (m, n) - 5 / 4 < 0 := by
  have hlow : -(1 / (N : ℝ)) ≤ x (m, n) := by
    have hη := robustTolerance_le_inv_N M hN
    have hx := (abs_le.mp hn).1
    linarith
  have hm := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ (N : ℝ) / 8 by positivity)
  have heq : (N : ℝ) / 8 * (-(1 / (N : ℝ))) = -(1 / 8) := by field_simp
  rw [heq] at hm
  have hc := tiltIntercept_lt (K := M * N) (r := m.val * N + n.val)
  linarith

/-- Any moved hidden coordinate identifies the attaining branch's facet
and gives that block a strictly positive optimizer weight. -/
theorem source_moving_hidden_facet {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N)
    (hmove : y (m, n) < x (m, n)) :
    x ≠ y ∧ a m = some n ∧ 0 < w m := by
  have hxy : x ≠ y := by intro h; rw [h] at hmove; exact (lt_irrefl _ hmove)
  have ha : a m = some n := by
    by_contra hne
    have heq := remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive m n hn hne
    linarith
  have hd := remote_source_hidden_displacement hM hN hy hxy w hw a hactive m n hn ha
  have hR : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  refine ⟨hxy, ha, ?_⟩
  nlinarith

/-- A moved hidden facet behind a closed gate forces the strict curvature
inequality used in the adjacent-front perturbation. -/
theorem source_moving_closed_gate_curvature {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : |x (m, n)| ≤ robustTolerance M N)
    (hmove : y (m, n) < x (m, n)) (hgate : precedingGate y m = 0) :
    64 * ‖positiveCoupledScores y‖ < (N : ℝ) * ‖x - y‖ := by
  have hnupper := (abs_le.mp hn).2
  obtain ⟨hxy, ha, hwm⟩ := source_moving_hidden_facet hM hN hy w hw a hactive m n hnupper hmove
  have hS := source_positive_score_norm_of_hidden hN hy m n hnupper
  have hscore := source_active_weight_score_pos hN hy w hw a hactive m n hnupper hwm
  have hweight := active_branch_weighted_score hN y hS w hw a hactive m
  rw [max_eq_left hscore.le] at hweight
  have hfacet := activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive m hwm
  have hfan : tiltedBlock N (M * N) m.val (coupledBlock y m) =
      fanPiece N (M * N) m.val (coupledBlock y m) n := by
    calc
      _ = euclideanTiltedBlock N (M * N) m.val (euclideanBlock y m) := rfl
      _ = affineFacet N (M * N) m.val (a m) (euclideanBlock y m) := hfacet.symm
      _ = _ := by rw [ha]; rfl
  have hscoreEq : coupledScore y m =
      tiltIntercept (M * N) (m.val * N + n.val) - (N : ℝ) / 8 * y (m, n) - 5 / 4 := by
    rw [coupledScore, hgate, hfan]
    simp only [fanPiece, coupledBlock, add_zero]
  have hd := remote_source_hidden_displacement hM hN hy hxy w hw a hactive m n hnupper ha
  have hb := hidden_query_fan_baseline_neg hN x m n hn
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hineq : ‖positiveCoupledScores y‖ * w m <
      ((N : ℝ) * ‖x - y‖ / 64) * w m := by
    rw [hweight, hscoreEq]
    nlinarith [hd]
  have hcancel := (mul_lt_mul_iff_left₀ hwm).mp hineq
  linarith

theorem hidden_query_block_tilt_le {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (m : Fin M)
    (hidden : ∀ n, |x (m, n)| ≤ robustTolerance M N) :
    tiltedBlock N (M * N) m.val (coupledBlock x m) ≤ 37 / 32 := by
  apply tiltedBlock_le (by norm_num)
  intro n
  have hlow : -(1 / (N : ℝ)) ≤ x (m, n) := by
    have hη := robustTolerance_le_inv_N M hN
    have hx := (abs_le.mp (hidden n)).1
    linarith
  have hm := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ (N : ℝ) / 8 by positivity)
  have heq : (N : ℝ) / 8 * (-(1 / (N : ℝ))) = -(1 / 8) := by field_simp
  rw [heq] at hm
  have hc := tiltIntercept_lt (K := M * N) (r := m.val * N + n.val)
  dsimp only [fanPiece, coupledBlock]
  linarith

/-- Swapping a future displacement into a hidden front coordinate rules
out the nonpositive-front and high-front-facet cases at once. -/
theorem source_front_swap_contradiction {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (front next : Fin M) (hfront : front.val < next.val) (k n : Fin N)
    (hk : |x (front, k)| ≤ robustTolerance M N)
    (hiddenNext : ∀ j, |x (next, j)| ≤ robustTolerance M N)
    (hmove : y (next, n) < x (next, n))
    (hgate : precedingGate y next = 0)
    (hfixed : y (front, k) = x (front, k))
    (hfrontscore : max (coupledScore y front) 0 ≤ precedingGate y front) : False := by
  have hn := hiddenNext n
  have hkupper := (abs_le.mp hk).2
  have hnupper := (abs_le.mp hn).2
  have hfn : front ≠ next := by intro h; subst next; exact lt_irrefl _ hfront
  obtain ⟨hxy, ha, hwm⟩ := source_moving_hidden_facet hM hN hy w hw a hactive next n hnupper hmove
  have hle := chain_source_coord_le hN hy
  let y' := swappedDisplacementSource x y (front, k) (next, n)
  have hfanEq := activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive next hwm
  have hfan : tiltedBlock N (M * N) next.val (coupledBlock y next) =
      fanPiece N (M * N) next.val (coupledBlock y next) n := by
    calc
      _ = euclideanTiltedBlock N (M * N) next.val (euclideanBlock y next) := rfl
      _ = affineFacet N (M * N) next.val (a next) (euclideanBlock y next) := hfanEq.symm
      _ = _ := by rw [ha]; rfl
  have hrank : front.val * N + k.val < next.val * N + n.val := by
    calc
      _ < front.val * N + N := Nat.add_lt_add_left k.isLt _
      _ = (front.val + 1) * N := by ring
      _ ≤ next.val * N := Nat.mul_le_mul_right N hfront
      _ ≤ _ := Nat.le_add_right _ _
  have horder := robust_tilt_order_strict hN hrank hk hn
  have hpiece : fanPiece N (M * N) next.val (coupledBlock y next) n <
      fanPiece N (M * N) front.val (coupledBlock y' front) k := by
    dsimp only [y', fanPiece, coupledBlock]
    rw [swappedDisplacementSource_left]
    nlinarith [horder]
  have hscoreNext : 0 < coupledScore y next :=
    source_active_weight_score_pos hN hy w hw a hactive next n hnupper hwm
  have hnewFront : coupledScore y next + precedingGate y front < coupledScore y' front := by
    have hlower := fanPiece_le_tiltedBlock N (M * N) front.val (coupledBlock y' front) k
    unfold coupledScore
    rw [hgate, hfan]
    dsimp only [y']
    rw [swappedDisplacementSource_gate hM hN hle (front, k) (next, n) hkupper hnupper]
    linarith
  have hnextBlock : coupledBlock y' next = coupledBlock x next := by
    funext j
    by_cases hj : j = n
    · subst j
      change swappedDisplacementSource x y (front, k) (next, n) (next, n) = x (next, n)
      rw [swappedDisplacementSource_right, hfixed]
      ring
    · have hnot : a next ≠ some j := by rw [ha]; exact fun h => hj (Option.some.inj h).symm
      have hjfixed := remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive
        next j (abs_le.mp (hiddenNext j)).2 hnot
      change swappedDisplacementSource x y (front, k) (next, n) (next, j) = x (next, j)
      rw [swappedDisplacementSource_other]
      · exact hjfixed
      · exact fun h => hfn (congrArg Prod.fst h).symm
      · exact fun h => hj (congrArg Prod.snd h)
  have hnewNext : coupledScore y' next < 0 := by
    unfold coupledScore
    dsimp only [y'] at hnextBlock ⊢
    rw [swappedDisplacementSource_gate hM hN hle (front, k) (next, n) hkupper hnupper,
      hgate, hnextBlock]
    have hbound := hidden_query_block_tilt_le hN x next hiddenNext
    linarith
  have hnormgain : ‖positiveCoupledScores y‖ < ‖positiveCoupledScores y'‖ := by
    apply positive_pair_trade_norm_strict (positiveCoupledScores y) (positiveCoupledScores y') hfn
    · intro m; exact le_max_right _ _
    · intro m; exact le_max_right _ _
    · change max (coupledScore y' next) 0 = 0
      exact max_eq_right hnewNext.le
    · change max (coupledScore y front) 0 + max (coupledScore y next) 0 < max (coupledScore y' front) 0
      rw [max_eq_left hscoreNext.le]
      simpa only [add_comm] using
        (add_le_add_right hfrontscore _).trans_lt (hnewFront.trans_le (le_max_left _ (0 : ℝ)))
    · intro m hmf hmn
      change max (coupledScore y' m) 0 = max (coupledScore y m) 0
      rw [show coupledScore y' m = coupledScore y m from
        swappedDisplacementSource_score_other hM hN hle (front, k) (next, n) hkupper hnupper m hmf hmn]
  have hprogress : (∑ j, blockProgress (coupledBlock y' j)) = ∑ j, blockProgress (coupledBlock y j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact swappedDisplacementSource_progress hM hN hle (front, k) (next, n) hkupper hnupper j
  have hf : coupledFunction y < coupledFunction y' := by
    unfold coupledFunction
    rw [hprogress]
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hnormgain _) (by positivity)
  have hdistance : ‖x - y'‖ = ‖x - y‖ := swappedDisplacementSource_distance x y (front, k) (next, n)
  have hupper := payoff_le_majorant (chainMajorant_finite hN) x y'
  change coupledFunction y - 2 * ‖x - y‖ = lipschitzMajorant coupledFunction 2 x at hy
  change coupledFunction y' - 2 * ‖x - y'‖ ≤ lipschitzMajorant coupledFunction 2 x at hupper
  rw [hdistance] at hupper
  linarith

end WC
