import WC.CoupledCurvature

/-! The actual terminal set, zero-score characterization and raw minimizers. -/

noncomputable section
namespace WC
open scoped BigOperators

def terminalRegion {M N : ℕ} : Set (ChainSpace M N) :=
  {x | ∀ (m : Fin M) (n : Fin N), fanPiece N (M * N) m.val (coupledBlock x m) n ≤ 1 / 4}

theorem blockProgress_one_of_small_fan {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N)
    (m : Fin M) (hf : tiltedBlock N (M * N) m.val (coupledBlock x m) ≤ 1 / 4) :
    blockProgress (coupledBlock x m) = 1 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htheta : 1 / (64 * (N : ℝ)) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity : 0 < 64 * (N : ℝ))).mpr (by nlinarith)
  have hterms (n : Fin N) :
      progressGate ((N : ℝ) / 4 * coupledBlock x m n - 1 / (64 * (N : ℝ))) = 1 := by
    have hrank : m.val * N + n.val < M * N := by
      calc
        _ < m.val * N + N := Nat.add_lt_add_left n.isLt _
        _ = (m.val + 1) * N := by ring
        _ ≤ M * N := Nat.mul_le_mul_right N m.isLt
    have hc := tiltIntercept_gt_one hrank
    have hp := (fanPiece_le_tiltedBlock N (M * N) m.val (coupledBlock x m) n).trans hf
    unfold fanPiece at hp
    apply progressGate_of_one_le
    nlinarith
  unfold blockProgress
  simp only [hterms, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (ne_of_gt hpos)

theorem terminalRegion_iff_coordinates {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    x ∈ terminalRegion ↔ ∀ (m : Fin M) (n : Fin N),
      8 * (tiltIntercept (M * N) (m.val * N + n.val) - 1 / 4) / (N : ℝ) ≤ x (m, n) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hx m n
    apply (div_le_iff₀ hpos).mpr
    have hp := hx m n
    dsimp [fanPiece, coupledBlock] at hp
    nlinarith
  · intro hx m n
    have hp := (div_le_iff₀ hpos).mp (hx m n)
    dsimp [fanPiece, coupledBlock]
    nlinarith

theorem terminalRegion_of_scores_nonpos {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N)
    (hs : ∀ m, coupledScore x m ≤ 0) : x ∈ terminalRegion := by
  have hprefix : ∀ j : ℕ, ∀ hj : j < M,
      blockProgress (coupledBlock x ⟨j, hj⟩) = 1 ∧
      tiltedBlock N (M * N) j (coupledBlock x ⟨j, hj⟩) ≤ 1 / 4 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have hgate : precedingGate x ⟨j, hj⟩ = 1 := by
        by_cases hzero : j = 0
        · simp [precedingGate, hzero]
        · have hjpos : 0 < j := Nat.pos_of_ne_zero hzero
          have hp := (ih (j - 1) (Nat.sub_lt hjpos (by norm_num))
            (lt_of_le_of_lt (Nat.sub_le _ _) hj)).1
          unfold precedingGate
          rw [if_neg hzero, hp]
          norm_num
      have hfan : tiltedBlock N (M * N) j (coupledBlock x ⟨j, hj⟩) ≤ 1 / 4 := by
        have h := hs ⟨j, hj⟩
        unfold coupledScore at h
        rw [hgate] at h
        linarith
      exact ⟨blockProgress_one_of_small_fan hN x ⟨j, hj⟩ hfan, hfan⟩
  intro m n
  exact (fanPiece_le_tiltedBlock N (M * N) m.val (coupledBlock x m) n).trans
    (hprefix m.val m.isLt).2

theorem terminalRegion_progress_one {M N : ℕ} (hN : 0 < N) {x : ChainSpace M N}
    (hx : x ∈ terminalRegion) (m : Fin M) : blockProgress (coupledBlock x m) = 1 := by
  apply blockProgress_one_of_small_fan hN x m
  exact tiltedBlock_le (by norm_num) (hx m)

theorem terminalRegion_scores_nonpos {M N : ℕ} (hN : 0 < N) {x : ChainSpace M N}
    (hx : x ∈ terminalRegion) (m : Fin M) : coupledScore x m ≤ 0 := by
  have hfan : tiltedBlock N (M * N) m.val (coupledBlock x m) ≤ 1 / 4 :=
    tiltedBlock_le (by norm_num) (hx m)
  have hgate : precedingGate x m = 1 := by
    unfold precedingGate
    split_ifs
    · rfl
    · rw [terminalRegion_progress_one hN hx]
      norm_num
  unfold coupledScore
  rw [hgate]
  linarith

theorem positiveCoupledScores_norm_eq_zero_iff {M N : ℕ} (x : ChainSpace M N) :
    ‖positiveCoupledScores x‖ = 0 ↔ ∀ m, coupledScore x m ≤ 0 := by
  rw [norm_eq_zero]
  constructor
  · intro h m
    have hc := congrArg (fun z : EuclideanSpace ℝ (Fin M) => z m) h
    change max (coupledScore x m) 0 = 0 at hc
    exact (le_max_left _ _).trans (le_of_eq hc)
  · intro h
    apply PiLp.ext
    intro m
    change max (coupledScore x m) 0 = 0
    exact max_eq_right (h m)

theorem positiveCoupledScores_norm_eq_zero_iff_terminalRegion {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) : ‖positiveCoupledScores x‖ = 0 ↔ x ∈ terminalRegion :=
  (positiveCoupledScores_norm_eq_zero_iff x).trans
    ⟨terminalRegion_of_scores_nonpos hN x, fun hx => terminalRegion_scores_nonpos hN hx⟩

theorem coupledFunction_eq_minimum_iff_terminalRegion {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) : coupledFunction x = -(4 * (M : ℝ) / N) ↔ x ∈ terminalRegion := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hx
    have hs : (∑ m : Fin M, blockProgress (coupledBlock x m)) ≤ M := by
      calc
        _ ≤ ∑ _ : Fin M, (1 : ℝ) := Finset.sum_le_sum fun m _ => blockProgress_le_one hN _
        _ = M := by simp
    have heq : coupledFunction x + 4 * (M : ℝ) / N = (2 / (N : ℝ)) *
        (‖positiveCoupledScores x‖ + 2 * ((M : ℝ) - ∑ m, blockProgress (coupledBlock x m))) := by
      unfold coupledFunction
      ring
    rw [hx] at heq
    have hzero : ‖positiveCoupledScores x‖ = 0 := by
      have hprod : (2 / (N : ℝ)) * (‖positiveCoupledScores x‖ +
          2 * ((M : ℝ) - ∑ m, blockProgress (coupledBlock x m))) = 0 := by linarith
      have hinside := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (by positivity : 0 < 2 / (N : ℝ)))
      nlinarith [norm_nonneg (positiveCoupledScores x)]
    exact (positiveCoupledScores_norm_eq_zero_iff_terminalRegion hN x).mp hzero
  · intro hx
    have hn := (positiveCoupledScores_norm_eq_zero_iff_terminalRegion hN x).mpr hx
    unfold coupledFunction
    rw [hn]
    simp only [terminalRegion_progress_one hN hx, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring

/-- The terminal polyhedron is exactly the global minimizer set of the raw function. -/
theorem coupledFunction_minimizers {M N : ℕ} (hN : 0 < N) :
    {x : ChainSpace M N | ∀ y : ChainSpace M N, coupledFunction x ≤ coupledFunction y} = terminalRegion := by
  ext x
  constructor
  · intro hx
    have h := hx (constantCompletion M N)
    rw [coupledFunction_completion hN] at h
    exact (coupledFunction_eq_minimum_iff_terminalRegion hN x).mp
      (le_antisymm h (coupledFunction_lower_bound hN x))
  · intro hx y
    rw [(coupledFunction_eq_minimum_iff_terminalRegion hN x).mpr hx]
    exact coupledFunction_lower_bound hN y

end WC
