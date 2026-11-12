import WCLB.Locality
import WCLB.Construction
import WC.RegroupedSubdifferential

/-! Certificates for the block relay, active weights, Fact 1, Lemma 8, and the inactive set in
Lemma 9 of WC.pdf. A layer index `r` denotes manuscript time `t = r - 1`,
including the empty prefix at `r = 0`. Coordinate and block indices start at zero. -/

noncomputable section
namespace WCLB
open WC
open scoped Classical

/-- Both activity thresholds in Remark 3 for a block whose coordinates are zero. -/
theorem unstarted_relay_thresholds {M N : ℕ} (hn : 0 < N) (z : ChainSpace M N)
    (m j : Fin M) (hj : j.val = m.val + 1) (hz : coupledBlock z j = fun _ => 0) :
    (blockProgress (coupledBlock z m) ≤ 1/4 → coupledScore z j < 0) ∧
    (1/2 ≤ blockProgress (coupledBlock z m) → 0 < coupledScore z j) := by
  have hgate : precedingGate z j = currentBlockGate z m := by
    simp only [precedingGate, if_neg (show j.val ≠ 0 by omega), currentBlockGate]
    congr 5
    apply congrArg (coupledBlock z)
    apply Fin.ext
    change j.val - 1 = m.val
    omega
  have hrank := Nat.mul_lt_mul_of_pos_right j.isLt hn
  rw [coupledScore, hz, tiltedBlock_zero_eq_first hn hrank, hgate]
  constructor
  · intro h
    have hzero : currentBlockGate z m = 0 := relayGate_zero h
    rw [hzero]
    linarith [tiltIntercept_lt (K := M * N) (r := j.val * N)]
  · intro h
    have hq : progressGate (1/3) = 7/27 := by norm_num [progressGate]
    have hmono := monotone_progressGate (show (1/3 : ℝ) ≤ (4*blockProgress (coupledBlock z m)-1)/3 by linarith)
    rw [hq] at hmono
    change 7/27 ≤ currentBlockGate z m at hmono
    linarith [tiltIntercept_gt_one hrank]

/-- The two active-weight clauses in Lemma 5, including literal singleton equality. -/
theorem active_weight_characterization {M N : ℕ} (z : ChainSpace M N) :
    (∀ w ∈ activeCoupledWeights z, ∀ m, coupledScore z m < 0 → w m = 0) ∧
    (positiveCoupledScores z ≠ 0 → activeCoupledWeights z =
      {‖positiveCoupledScores z‖⁻¹ • positiveCoupledScores z}) := by
  constructor
  · intro w hw m hm
    have hw0 := hw.1.1 m
    by_contra hne
    have hp := active_score_weight_nonneg (coupledScores z) w hw.1 hw.2 m (lt_of_le_of_ne hw0 (Ne.symm hne))
    exact hm.not_ge hp
  · intro hn
    have hP : positiveScores (coupledScores z) ≠ 0 := hn
    have heq : positiveScoreOptimizer (coupledScores z) = ‖positiveCoupledScores z‖⁻¹ • positiveCoupledScores z := by
      rw [positiveScoreOptimizer, if_neg hP]
      rfl
    rw [← heq]
    ext w
    constructor
    · intro hw
      exact positiveScoreOptimizer_unique _ (norm_pos_iff.mpr hP) w hw.1 hw.2
    · rintro rfl
      exact ⟨positiveScoreOptimizer_mem _, positiveScoreOptimizer_attains _⟩

/-- Zero-based index of the last started block (block zero for the empty prefix). -/
def lastStartedBlock (M N r : ℕ) : ℕ := min (M - 1) ((r - 1) / stagger N)

private theorem prefix_end_bound {M N r : ℕ} (hN : 256 ≤ N)
    (hk : lastStartedBlock M N r + 1 < M) : r ≤ (lastStartedBlock M N r + 1) * stagger N := by
  have h : (r - 1) / stagger N < M - 1 := by
    unfold lastStartedBlock at hk
    omega
  rw [lastStartedBlock, min_eq_right h.le]
  have hd := (Nat.div_lt_iff_lt_mul (stagger_pos hN)).mp (Nat.lt_succ_self ((r - 1) / stagger N))
  change r - 1 < ((r - 1) / stagger N + 1) * stagger N at hd
  omega

/-- Fact 1: hidden coordinates have flat progress at *every maximizing source*;
query facets are strictly ordered lexicographically, and gates past the front are closed. -/
theorem fact_one {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N) (r : ℕ)
    {z y : ChainSpace M N} (hidden : z ∈ diagonalTube M N r)
    (hy : y ∈ majorantSources coupledFunction 2 z) :
    (∀ i : Fin M × Fin N, i ∉ exposedIndices M N r →
      progressGate ((N : ℝ) / 4 * y i - 1 / (64 * N)) = 0 ∧
      deriv progressGate ((N : ℝ) / 4 * y i - 1 / (64 * N)) = 0) ∧
    (∀ i j : Fin M × Fin N, i ∉ exposedIndices M N r → j ∉ exposedIndices M N r →
      (i.1 < j.1 ∨ (i.1 = j.1 ∧ i.2 < j.2)) →
      fanPiece N (M*N) j.1.val (coupledBlock z j.1) j.2 <
        fanPiece N (M*N) i.1.val (coupledBlock z i.1) i.2) ∧
    (lastStartedBlock M N r + 1 < M →
      (∀ m : Fin M, lastStartedBlock M N r ≤ m.val → currentBlockGate y m = 0) ∧
      (∀ m : Fin M, lastStartedBlock M N r < m.val →
        tiltedBlock N (M*N) m.val (coupledBlock z m) < 5 / 4)) := by
  have hn : 0 < N := by omega
  have hh (i : Fin M × Fin N) (hi : i ∉ exposedIndices M N r) : |z i| ≤ robustTolerance M N := by
    apply le_of_lt (hidden i _)
    simpa [exposedIndices] using hi
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [deriv_progressGate]
    exact hidden_progress_and_slope_zero hM hn
      ((chain_source_coord_le hn hy i).trans ((le_abs_self _).trans (hh i hi)))
  · intro i j hi hj hlex
    apply robust_tilt_order_strict hn _ (hh i hi) (hh j hj)
    rcases hlex with h | ⟨h, h'⟩
    · calc
        i.1.val * N + i.2.val < i.1.val * N + N := Nat.add_lt_add_left i.2.isLt _
        _ = (i.1.val + 1) * N := by ring
        _ ≤ j.1.val * N := Nat.mul_le_mul_right N h
        _ ≤ _ := Nat.le_add_right _ _
    · rw [h]
      exact Nat.add_lt_add_left h' _
  · intro hk
    have hend := prefix_end_bound hN hk
    constructor
    · intro m hm
      have hl : r ≤ (m.val + 1) * stagger N := hend.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ hm))
      rw [Nat.add_mul, Nat.one_mul] at hl
      let I : Finset (Fin N) := Finset.univ.filter fun n => n.val < stagger N
      have hc : I.card ≤ (Finset.range (stagger N)).card := by
        apply Finset.card_le_card_of_injOn (fun n : Fin N => n.val)
        · intro n hn'
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hn').2
        · intro i _ j _ heq
          exact Fin.ext heq
      simp only [Finset.card_range] at hc
      have h4 : 4 * stagger N ≤ N := by unfold stagger; omega
      apply relayGate_zero
      apply blockProgress_le_quarter_of_hidden hM hn (coupledBlock y m) I (by omega)
      intro n hn'
      have hs : stagger N ≤ n.val := by simpa [I] using hn'
      apply (chain_source_coord_le hn hy (m,n)).trans
      apply (le_abs_self _).trans
      exact (hidden (m,n) (by dsimp [diagonalLevel]; omega)).le
    · intro m hm
      have hl : r ≤ m.val * stagger N := hend.trans (Nat.mul_le_mul_right _ hm)
      apply (hidden_query_block_tilt_le hn z m (fun n =>
        (hidden (m,n) (by dsimp [diagonalLevel]; omega)).le)).trans_lt
      norm_num

/-- Lemma 8, stating the displacement assertion for each source itself. -/
theorem remote_source_displacement {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N) (r : ℕ)
    {z y : ChainSpace M N} (hidden : z ∈ diagonalTube M N r)
    (hy : y ∈ majorantSources coupledFunction 2 z) (hne : y ≠ z)
    (i : Fin M × Fin N) (hi : i ∉ exposedIndices M N (r + 1)) : (z - y) i = 0 := by
  have hn : 0 < N := by omega
  let g := (-2 / ‖z - y‖) • (z - y)
  have hg : g ∈ subdifferential coupledFunction y := by
    rw [remote_source_subdifferential hn hy hne.symm]
    exact Set.mem_singleton _
  have hg' : g ∈ subdifferential chainMajorant z := by
    rw [chainMajorant_subdifferential hN]
    exact subset_convexHull ℝ _ ⟨y, hy, hg⟩
  have hs := chainMajorant_subgradient_diagonal_zero hM hN z r
    (fun j hj => (hidden j hj).le) hg' i (by simpa [exposedIndices] using hi)
  change (-2 / ‖z - y‖) * (z - y) i = 0 at hs
  exact (mul_eq_zero.mp hs).resolve_left (div_ne_zero (by norm_num) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)))

/-- The paper defines Z by nonpositive block scores, rather than by fan inequalities. -/
def inactiveSet (M N : ℕ) : Set (ChainSpace M N) := {x | ∀ m, coupledScore x m ≤ 0}

theorem inactiveSet_eq_terminalRegion {M N : ℕ} (hn : 0 < N) :
    inactiveSet M N = terminalRegion := by
  ext x
  exact ⟨terminalRegion_of_scores_nonpos hn x, terminalRegion_scores_nonpos hn⟩

/-- Lemma 9(i): the coordinate bound is strict; the distance bound is for any
selection of at least `N` small coordinates and is expressed using actual infimum distance. -/
theorem terminal_geometry {M N : ℕ} (hn : 0 < N) :
    (∀ x ∈ inactiveSet M N, ∀ i : Fin M × Fin N, 6 / (N : ℝ) < x i) ∧
    (∀ (z : ChainSpace M N) (s : Finset (Fin M × Fin N)), N ≤ s.card →
      (∀ i ∈ s, z i ≤ robustTolerance M N) → 5 / Real.sqrt (N : ℝ) ≤ Metric.infDist z (inactiveSet M N)) := by
  rw [inactiveSet_eq_terminalRegion hn]
  constructor
  · intro x hx i
    have hpos : (0 : ℝ) < N := by exact_mod_cast hn
    have hrank : i.1.val * N + i.2.val < M * N := by
      calc
        _ < i.1.val * N + N := Nat.add_lt_add_left i.2.isLt _
        _ = (i.1.val + 1) * N := by ring
        _ ≤ _ := Nat.mul_le_mul_right N i.1.isLt
    have hc := tiltIntercept_gt_one hrank
    have hp := hx i.1 i.2
    dsimp [fanPiece, coupledBlock] at hp
    apply (div_lt_iff₀ hpos).mpr
    nlinarith
  · intro z s hcard hsmall
    apply (Metric.le_infDist (terminalRegion_nonempty hn)).mpr
    intro q hq
    rw [dist_eq_norm]
    exact terminal_distance_lower_of_small_coordinates hn z q hq s hcard
      (fun i hi => (hsmall i hi).trans (robustTolerance_le_inv_N M hn))

end WCLB
