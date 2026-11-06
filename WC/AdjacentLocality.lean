import WC.FlatFrontLocality

/-! Every source is fixed on every entirely hidden block with a closed
predecessor gate and at least one hidden predecessor coordinate. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

theorem source_hidden_fixed_of_weight_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x) (hxy : x ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (a : Fin M → FanFacet N) (hactive : coupledFacetBranch w a y = coupledFunction y)
    (m : Fin M) (n : Fin N) (hn : x (m, n) ≤ robustTolerance M N) (hwm : w m = 0) :
    y (m, n) = x (m, n) := by
  by_cases ha : a m = some n
  · have hd := remote_source_hidden_displacement hM hN hy hxy w hw a hactive m n hn ha
    rw [hwm] at hd
    linarith
  · exact remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive m n hn ha

/-- The adjacent-front argument excludes motion in a hidden future block
for every maximizing source, independently of all other future blocks. -/
theorem source_hidden_next_fixed {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (front next : Fin M) (hnext : next.val = front.val + 1) (k : Fin N)
    (hk : |x (front, k)| ≤ robustTolerance M N)
    (hiddenNext : ∀ n, |x (next, n)| ≤ robustTolerance M N)
    (hprogress : blockProgress (coupledBlock y front) ≤ 1 / 4) :
    ∀ n, y (next, n) = x (next, n) := by
  intro n
  have hle := chain_source_coord_le hN hy
  apply le_antisymm (hle (next, n))
  by_contra hnot
  have hmove : y (next, n) < x (next, n) := lt_of_not_ge hnot
  obtain ⟨w, hw, a, hactive⟩ := coupledFacetBranch_attains_coupledFunction y
  have hnupper := (abs_le.mp (hiddenNext n)).2
  have hkupper := (abs_le.mp hk).2
  obtain ⟨hxy, han, hβ⟩ := source_moving_hidden_facet hM hN hy w hw a hactive next n hnupper hmove
  have hgate := nextGate_zero_of_front_progress y front next hnext hprogress
  have hfront : front.val < next.val := by omega
  have hfn : front ≠ next := by intro h; subst next; omega
  have hS := remote_source_positive_scores hN hy hxy
  have hcurvature := source_moving_closed_gate_curvature hM hN hy w hw a hactive
    next n (hiddenNext n) hmove hgate
  by_cases hα : 0 < w front
  · have hfanEq := activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive front hα
    have haf_some : ∃ j, a front = some j := by
      cases hfa : a front with
      | none =>
        have hpositive := hidden_fanPiece_gt_quarter hN y front k ((hle (front, k)).trans hkupper)
        have hbound := fanPiece_le_tiltedBlock N (M * N) front.val (coupledBlock y front) k
        rw [hfa] at hfanEq
        change (0 : ℝ) = tiltedBlock N (M * N) front.val (coupledBlock y front) at hfanEq
        linarith
      | some j => exact ⟨j, rfl⟩
    obtain ⟨j, haf⟩ := haf_some
    by_cases hflat : y (front, j) ≤ progressThreshold N
    · exact source_flat_front_contradiction hM hN hy hxy w hw a hactive front next hfn j n
        haf han hα hβ hflat ((hle (next, n)).trans hnupper) hcurvature
    · have hhigh : progressThreshold N < y (front, j) := lt_of_not_ge hflat
      have hη := robustTolerance_lt_progressThreshold hM hN
      have hjk : j ≠ k := by
        intro h
        subst j
        have hh := hle (front, k)
        linarith
      have hnotfacet : a front ≠ some k := by rw [haf]; exact fun h => hjk (Option.some.inj h)
      have hfixed := remote_source_hidden_unchanged_of_not_facet hM hN hy hxy w hw a hactive
        front k hkupper hnotfacet
      have hfan : tiltedBlock N (M * N) front.val (coupledBlock y front) =
          fanPiece N (M * N) front.val (coupledBlock y front) j := by
        calc
          _ = euclideanTiltedBlock N (M * N) front.val (euclideanBlock y front) := rfl
          _ = affineFacet N (M * N) front.val (a front) (euclideanBlock y front) := hfanEq.symm
          _ = _ := by rw [haf]; rfl
      have hsourcepos : 0 < y (front, j) := by
        have ht : 0 < progressThreshold N := by unfold progressThreshold; positivity
        exact ht.trans hhigh
      have hscore : coupledScore y front < precedingGate y front := by
        rw [coupledScore, hfan]
        have hc := tiltIntercept_lt (K := M * N) (r := front.val * N + j.val)
        have hm : 0 ≤ (N : ℝ) / 8 * y (front, j) := by positivity
        dsimp only [fanPiece, coupledBlock]
        linarith
      have hmax : max (coupledScore y front) 0 ≤ precedingGate y front :=
        max_le hscore.le (precedingGate_nonneg y front)
      exact source_front_swap_contradiction hM hN hy w hw a hactive front next hfront k n hk
        hiddenNext hmove hgate hfixed hmax
  · have hzero : w front = 0 := le_antisymm (le_of_not_gt hα) (hw.1 front)
    have hfixed := source_hidden_fixed_of_weight_zero hM hN hy hxy w hw a hactive front k hkupper hzero
    have hweight := active_branch_weighted_score hN y hS w hw a hactive front
    rw [hzero, mul_zero] at hweight
    have hmax : max (coupledScore y front) 0 ≤ precedingGate y front := by
      rw [← hweight]
      exact precedingGate_nonneg y front
    exact source_front_swap_contradiction hM hN hy w hw a hactive front next hfront k n hk
      hiddenNext hmove hgate hfixed hmax

theorem source_subgradient_hidden_next_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {x y v : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (hv : v ∈ subdifferential coupledFunction y)
    (front next : Fin M) (hnext : next.val = front.val + 1) (k : Fin N)
    (hk : |x (front, k)| ≤ robustTolerance M N)
    (hiddenNext : ∀ n, |x (next, n)| ≤ robustTolerance M N)
    (hprogress : blockProgress (coupledBlock y front) ≤ 1 / 4) (n : Fin N) : v (next, n) = 0 := by
  have hfixed := source_hidden_next_fixed hM hN hy front next hnext k hk hiddenNext hprogress n
  by_cases hxy : x ≠ y
  · have hg := chain_remote_source_subgradient hN hy hxy hv
    have hc := congrArg (fun g : ChainSpace M N => g (next, n)) hg
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hfixed, sub_self, mul_zero] at hc
    exact hc
  · have heq : x = y := not_ne_iff.mp hxy
    subst y
    have hgate := nextGate_zero_of_front_progress x front next hnext hprogress
    have hscore : coupledScore x next < 0 := by
      unfold coupledScore
      rw [hgate]
      have hh := hidden_query_block_tilt_le hN x next hiddenNext
      linarith
    rw [subdifferential_coupledFunction_eq_convexHull hN] at hv
    have hconv : Convex ℝ {g : ChainSpace M N | g (next, n) = 0} := by
      intro g hg h hh s t _ _ _
      change s * g (next, n) + t * h (next, n) = 0
      simp only [Set.mem_setOf_eq] at hg hh
      simp [hg, hh]
    have hgen : coupledActiveGradients x ⊆ {g : ChainSpace M N | g (next, n) = 0} := by
      rintro g ⟨w, hw, a, hactive, rfl⟩
      have hS := source_positive_score_norm_of_hidden hN hy next n (abs_le.mp (hiddenNext n)).2
      have hh := active_branch_weighted_score hN x hS w hw a hactive next
      rw [max_eq_right hscore.le] at hh
      have hwzero : w next = 0 := (mul_eq_zero.mp hh).resolve_left hS.ne'
      have hgrad := coupled_branch_gradient_hidden hM hN w a x next n (abs_le.mp (hiddenNext n)).2
      change coupledFacetBranchGradient w a x (next, n) = 0
      rw [hgrad]
      split_ifs <;> simp [hwzero]
    exact convexHull_min hgen hconv hv

/-- Actual full majorant subgradients vanish on the entire next hidden
block as long as at most one quarter of its predecessor is exposed. -/
theorem chainMajorant_subgradient_hidden_next_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    {x v : ChainSpace M N} (hv : v ∈ subdifferential chainMajorant x)
    (front next : Fin M) (hnext : next.val = front.val + 1)
    (I : Finset (Fin N)) (hcard : 4 * I.card ≤ N)
    (hiddenFront : ∀ n, n ∉ I → |x (front, n)| ≤ robustTolerance M N)
    (hiddenNext : ∀ n, |x (next, n)| ≤ robustTolerance M N) (n : Fin N) : v (next, n) = 0 := by
  have hNpos : 0 < N := by omega
  have hcardlt : I.card < N := by omega
  have hk : ∃ k : Fin N, k ∉ I := by
    by_contra h
    have hall : I = Finset.univ := Finset.eq_univ_of_forall (fun k => by simpa using not_exists.mp h k)
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcardlt
    omega
  obtain ⟨k, hk⟩ := hk
  rw [chainMajorant_subdifferential hN] at hv
  have hconv : Convex ℝ {g : ChainSpace M N | g (next, n) = 0} := by
    intro g hg h hh s t _ _ _
    change s * g (next, n) + t * h (next, n) = 0
    simp only [Set.mem_setOf_eq] at hg hh
    simp [hg, hh]
  have hslopes : sourceSlopes coupledFunction 2 x ⊆ {g : ChainSpace M N | g (next, n) = 0} := by
    rintro g ⟨y, hy, hg⟩
    have hle := chain_source_coord_le hNpos hy
    have hprogress : blockProgress (coupledBlock y front) ≤ 1 / 4 :=
      blockProgress_le_quarter_of_hidden hM hNpos (coupledBlock y front) I hcard
        (fun j hj => (hle (front, j)).trans (abs_le.mp (hiddenFront j hj)).2)
    exact source_subgradient_hidden_next_zero hM hNpos hy hg front next hnext k
      (hiddenFront k hk) hiddenNext hprogress n
  exact convexHull_min hslopes hconv hv

end WC
