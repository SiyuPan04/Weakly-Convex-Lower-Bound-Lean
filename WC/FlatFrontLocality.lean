import WC.FrontLocality
import WC.FrontPerturbation

/-! The actual local two-facet perturbation at a remote maximizing source. -/

noncomputable section
namespace WC
open scoped BigOperators Classical
open Filter Topology

theorem pairShift_progress_eq_of_flat {M N : ℕ} (hN : 0 < N)
    (y : ChainSpace M N) (i j : Fin M × Fin N) (u v t : ℝ)
    (hi : y i ≤ progressThreshold N) (hj : y j ≤ progressThreshold N)
    (hi' : pairShift y i j u v t i ≤ progressThreshold N)
    (hj' : pairShift y i j u v t j ≤ progressThreshold N) (m : Fin M) :
    blockProgress (coupledBlock (pairShift y i j u v t) m) = blockProgress (coupledBlock y m) := by
  unfold blockProgress
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hni : (m, n) = i
  · change progressGate ((N : ℝ) / 4 * pairShift y i j u v t (m, n) - _) =
      progressGate ((N : ℝ) / 4 * y (m, n) - _)
    rw [hni, (progress_term_zero_of_le_threshold hN hi').1,
      (progress_term_zero_of_le_threshold hN hi).1]
  · by_cases hnj : (m, n) = j
    · change progressGate ((N : ℝ) / 4 * pairShift y i j u v t (m, n) - _) =
        progressGate ((N : ℝ) / 4 * y (m, n) - _)
      rw [hnj, (progress_term_zero_of_le_threshold hN hj').1,
        (progress_term_zero_of_le_threshold hN hj).1]
    · change progressGate ((N : ℝ) / 4 * pairShift y i j u v t (m, n) - _) =
        progressGate ((N : ℝ) / 4 * y (m, n) - _)
      rw [pairShift_other y i j (m, n) hni hnj]

theorem pairShift_gate_eq_of_progress {M N : ℕ}
    (y : ChainSpace M N) (i j : Fin M × Fin N) (u v t : ℝ)
    (hp : ∀ m, blockProgress (coupledBlock (pairShift y i j u v t) m) = blockProgress (coupledBlock y m))
    (m : Fin M) : precedingGate (pairShift y i j u v t) m = precedingGate y m := by
  unfold precedingGate
  split_ifs
  · rfl
  · rw [hp]

theorem pairShift_score_other {M N : ℕ}
    (y : ChainSpace M N) (i j : Fin M × Fin N) (u v t : ℝ)
    (hp : ∀ m, blockProgress (coupledBlock (pairShift y i j u v t) m) = blockProgress (coupledBlock y m))
    (m : Fin M) (hmi : m ≠ i.1) (hmj : m ≠ j.1) :
    coupledScore (pairShift y i j u v t) m = coupledScore y m := by
  have hb : coupledBlock (pairShift y i j u v t) m = coupledBlock y m := by
    funext n
    exact pairShift_other y i j (m, n) (fun h => hmi (congrArg Prod.fst h))
      (fun h => hmj (congrArg Prod.fst h)) u v t
  rw [coupledScore, hb, pairShift_gate_eq_of_progress y i j u v t hp]
  rfl

theorem continuous_pairShift_curve {ι : Type*} [Fintype ι]
    (y : EuclideanSpace ℝ ι) (i j : ι) (u v : ℝ) :
    Continuous (fun t : ℝ => pairShift y i j u v t) := by
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- If both active facets are progress-flat, the actual source cannot
have the strict front curvature ratio. Unique-facet persistence supplies
the genuine neighborhood formulas; no locality hypothesis is assumed. -/
theorem source_flat_front_contradiction {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x) (hxy : x ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (front next : Fin M) (hfn : front ≠ next) (k n : Fin N)
    (haf : a front = some k) (han : a next = some n)
    (hα : 0 < w front) (hβ : 0 < w next)
    (hflat : y (front, k) ≤ progressThreshold N)
    (hhidden : y (next, n) ≤ robustTolerance M N)
    (hcurvature : 64 * ‖positiveCoupledScores y‖ < (N : ℝ) * ‖x - y‖) : False := by
  let α := w front
  let β := w next
  let S := ‖positiveCoupledScores y‖
  let R := ‖x - y‖
  let curve : ℝ → ChainSpace M N := fun t => pairShift y (front, k) (next, n) (-β) α t
  have hij : (front, k) ≠ (next, n) := fun h => hfn (congrArg Prod.fst h)
  have hS : 0 < S := remote_source_positive_scores hN hy hxy
  have hR : 0 < R := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hη := robustTolerance_lt_progressThreshold hM hN
  have hnextflat : y (next, n) < progressThreshold N := hhidden.trans_lt hη
  have hα' : 0 < α := hα
  have hβ' : 0 < β := hβ
  have hfrontScore : 0 < coupledScore y front := by
    have hh := active_branch_weighted_score hN y hS w hw a hactive front
    have hp : 0 < max (coupledScore y front) 0 := by rw [← hh]; exact mul_pos hS hα
    exact (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
  have hnextScore : 0 < coupledScore y next := by
    have hh := active_branch_weighted_score hN y hS w hw a hactive next
    have hp : 0 < max (coupledScore y next) 0 := by rw [← hh]; exact mul_pos hS hβ
    exact (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
  have hcurve : Continuous curve := continuous_pairShift_curve y _ _ (-β) α
  have hcurve0 : curve 0 = y := by simp [curve, pairShift]
  have hfrontT : Tendsto (fun t => euclideanBlock (curve t) front) (𝓝 0) (𝓝 (euclideanBlock y front)) := by
    have hh := ((blockProjection front).continuous.comp hcurve).tendsto 0
    change Tendsto (fun t => euclideanBlock (curve t) front) (𝓝 0) (𝓝 (euclideanBlock (curve 0) front)) at hh
    rw [hcurve0] at hh
    exact hh
  have hnextT : Tendsto (fun t => euclideanBlock (curve t) next) (𝓝 0) (𝓝 (euclideanBlock y next)) := by
    have hh := ((blockProjection next).continuous.comp hcurve).tendsto 0
    change Tendsto (fun t => euclideanBlock (curve t) next) (𝓝 0) (𝓝 (euclideanBlock (curve 0) next)) at hh
    rw [hcurve0] at hh
    exact hh
  have hfEvent := hfrontT.eventually (remote_source_active_facet_eventually hN hy hxy w hw a hactive front hα)
  have hnEvent := hnextT.eventually (remote_source_active_facet_eventually hN hy hxy w hw a hactive next hβ)
  obtain ⟨ε₀, hε₀, hpersist⟩ := Metric.eventually_nhds_iff.mp (hfEvent.and hnEvent)
  let ε₁ := (progressThreshold N - y (next, n)) / α
  let ε₂ := coupledScore y next / ((N : ℝ) / 8 * α)
  have hε₁ : 0 < ε₁ := div_pos (sub_pos.mpr hnextflat) hα'
  have hε₂ : 0 < ε₂ := div_pos hnextScore (by positivity)
  let ε := min ε₀ (min ε₁ ε₂)
  have hε : 0 < ε := lt_min hε₀ (lt_min hε₁ hε₂)
  have hdf := remote_source_pure_fan_displacement hN hy hxy w hw a hactive front k haf
    (progressGradient_zero_of_le_threshold hN _ k hflat)
  have hdn := remote_source_pure_fan_displacement hN hy hxy w hw a hactive next n han
    (progressGradient_zero_of_hidden hM hN _ n hhidden)
  apply source_forbids_front_local_formulas hN hy curve (C := α ^ 2 + β ^ 2)
    hS hR (by nlinarith [sq_nonneg α, sq_pos_of_pos hβ']) rfl rfl hcurvature
  refine ⟨ε, hε, ?_⟩
  intro t ht htε
  have ht₀ : t < ε₀ := htε.trans_le (min_le_left _ _)
  have ht₁ : t < ε₁ := htε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₂ : t < ε₂ := htε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htf : curve t (front, k) ≤ progressThreshold N := by
    change pairShift y (front, k) (next, n) (-β) α t (front, k) ≤ _
    rw [pairShift_left y hij]
    nlinarith
  have htn : curve t (next, n) ≤ progressThreshold N := by
    change pairShift y (front, k) (next, n) (-β) α t (next, n) ≤ _
    rw [pairShift_right y hij]
    have hh := (lt_div_iff₀ hα').mp ht₁
    dsimp only [ε₁] at hh
    linarith
  have hp (m : Fin M) : blockProgress (coupledBlock (curve t) m) = blockProgress (coupledBlock y m) :=
    pairShift_progress_eq_of_flat hN y (front, k) (next, n) (-β) α t hflat hnextflat.le htf htn m
  have hg (m : Fin M) : precedingGate (curve t) m = precedingGate y m :=
    pairShift_gate_eq_of_progress y (front, k) (next, n) (-β) α t hp m
  have hpersistt := hpersist (y := t) (by simpa [Real.dist_eq, abs_of_pos ht] using ht₀)
  have hff := (hpersistt.1).1
  have hnf := (hpersistt.2).1
  have hff0 := activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive front hα
  have hnf0 := activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive next hβ
  have hsf : coupledScore (curve t) front = coupledScore y front + (N : ℝ) / 8 * β * t := by
    unfold coupledScore
    rw [hg]
    change euclideanTiltedBlock N (M * N) front.val (euclideanBlock (curve t) front) + _ - _ =
      euclideanTiltedBlock N (M * N) front.val (euclideanBlock y front) + _ - _ + _
    rw [← hff, ← hff0, haf]
    change tiltIntercept _ _ - (N : ℝ) / 8 * curve t (front, k) + _ - _ =
      tiltIntercept _ _ - (N : ℝ) / 8 * y (front, k) + _ - _ + _
    dsimp only [curve]
    rw [pairShift_left y hij]
    ring
  have hsn : coupledScore (curve t) next = coupledScore y next - (N : ℝ) / 8 * α * t := by
    unfold coupledScore
    rw [hg]
    change euclideanTiltedBlock N (M * N) next.val (euclideanBlock (curve t) next) + _ - _ =
      euclideanTiltedBlock N (M * N) next.val (euclideanBlock y next) + _ - _ - _
    rw [← hnf, ← hnf0, han]
    change tiltIntercept _ _ - (N : ℝ) / 8 * curve t (next, n) + _ - _ =
      tiltIntercept _ _ - (N : ℝ) / 8 * y (next, n) + _ - _ - _
    dsimp only [curve]
    rw [pairShift_right y hij]
    ring
  have hsfpos : 0 < coupledScore (curve t) front := by rw [hsf]; positivity
  have hsnpos : 0 < coupledScore (curve t) next := by
    rw [hsn]
    have hh := (lt_div_iff₀ (show 0 < (N : ℝ) / 8 * α by positivity)).mp ht₂
    dsimp only [ε₂] at hh
    nlinarith
  have hscores : positiveCoupledScores (curve t) =
      pairShift (positiveCoupledScores y) front next ((N : ℝ) / 8 * β) (-((N : ℝ) / 8 * α)) t := by
    apply PiLp.ext
    intro m
    by_cases hmf : m = front
    · subst m
      rw [pairShift_left _ hfn]
      change max (coupledScore (curve t) front) 0 = max (coupledScore y front) 0 + _
      rw [max_eq_left hsfpos.le, max_eq_left hfrontScore.le, hsf]
      ring
    · by_cases hmn : m = next
      · subst m
        rw [pairShift_right _ hfn]
        change max (coupledScore (curve t) next) 0 = max (coupledScore y next) 0 + _
        rw [max_eq_left hsnpos.le, max_eq_left hnextScore.le, hsn]
        ring
      · rw [pairShift_other _ front next m hmf hmn]
        change max (coupledScore (curve t) m) 0 = max (coupledScore y m) 0
        rw [show coupledScore (curve t) m = coupledScore y m from
          pairShift_score_other y (front, k) (next, n) (-β) α t hp m hmf hmn]
  have hpi : positiveCoupledScores y front = S * α := by
    exact (active_branch_weighted_score hN y hS w hw a hactive front).symm
  have hpj : positiveCoupledScores y next = S * β := by
    exact (active_branch_weighted_score hN y hS w hw a hactive next).symm
  refine ⟨Finset.sum_congr rfl (fun m _ => hp m), ?_, ?_⟩
  · rw [hscores, front_score_norm_sq _ hfn rfl hpi hpj]
    dsimp only [S]
    ring
  · exact front_source_distance_sq x y hij rfl hdf hdn t

end WC
