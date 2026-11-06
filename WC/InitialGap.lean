import WC.ChainMajorant

/-! The exact initial-gap certificate for the actual Lipschitz majorant. -/

noncomputable section
namespace WC
open scoped BigOperators

def chainMinimizer (M N : ℕ) : ChainSpace M N :=
  WithLp.toLp 2 (fun _ => 9 / (N : ℝ) + 16 * (M : ℝ) / (7 * (N : ℝ)))

theorem coupledFunction_le_positiveScoreTerm {M N : ℕ} (x : ChainSpace M N) :
    coupledFunction x ≤ positiveScoreTerm x := by
  have hs : 0 ≤ ∑ m, blockProgress (coupledBlock x m) :=
    Finset.sum_nonneg fun _ _ => blockProgress_nonneg _
  unfold coupledFunction positiveScoreTerm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem coupledFunction_zero_eq_positiveScoreTerm_zero {M N : ℕ} :
    coupledFunction (0 : ChainSpace M N) = positiveScoreTerm (0 : ChainSpace M N) := by
  simp only [coupledFunction, positiveScoreTerm, coupledBlock_zero, blockProgress_zero_fun,
    Finset.sum_const_zero, mul_zero, sub_zero]

theorem chainMajorant_zero {M N : ℕ} (hN : 256 ≤ N) :
    chainMajorant (0 : ChainSpace M N) = coupledFunction (0 : ChainSpace M N) := by
  have hpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  apply le_antisymm
  · change sSup (Set.range (sourcePayoff coupledFunction 2 (0 : ChainSpace M N))) ≤ _
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨y, rfl⟩
    have hf := coupledFunction_le_positiveScoreTerm y
    have hs := positiveScoreTerm_lipschitz_uniform hN y (0 : ChainSpace M N)
    simp only [sub_zero] at hs
    have hl := (le_abs_self (positiveScoreTerm y - positiveScoreTerm (0 : ChainSpace M N))).trans hs
    rw [← coupledFunction_zero_eq_positiveScoreTerm_zero] at hl
    dsimp [sourcePayoff]
    rw [zero_sub, norm_neg]
    nlinarith [norm_nonneg y]
  · exact coupledFunction_le_chainMajorant hpos 0

theorem coupledFunction_plateau {M N : ℕ} (hN : 0 < N) (y : ChainSpace M N)
    (hy : ∀ i, 9 / (N : ℝ) ≤ y i) : coupledFunction y = -(4 * (M : ℝ) / N) := by
  have ha := coupledFunction_coordinate_antitone (constantCompletion M N) y hy
  rw [coupledFunction_completion hN] at ha
  exact le_antisymm ha (coupledFunction_lower_bound hN y)

/-- The displayed `z_*` really attains the minimum after taking the majorant. -/
theorem chainMajorant_minimizer {M N : ℕ} (hN : 0 < N) :
    chainMajorant (chainMinimizer M N) = -(4 * (M : ℝ) / N) := by
  let z := chainMinimizer M N
  let Q : ℝ := 16 * (M : ℝ) / (7 * (N : ℝ))
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hz : ∀ i, 9 / (N : ℝ) ≤ z i := by
    intro i
    change 9 / (N : ℝ) ≤ 9 / (N : ℝ) + Q
    linarith
  apply le_antisymm
  · change sSup (Set.range (sourcePayoff coupledFunction 2 z)) ≤ -(4 * (M : ℝ) / N)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨y, rfl⟩
    by_cases hy : ∀ i, 9 / (N : ℝ) ≤ y i
    · have hp := coupledFunction_plateau hN y hy
      dsimp [sourcePayoff]
      rw [hp]
      linarith [norm_nonneg (z - y)]
    · obtain ⟨i, hi⟩ := not_forall.mp hy
      have hcoord := PiLp.norm_apply_le (z - y) i
      change ‖9 / (N : ℝ) + Q - y i‖ ≤ ‖z - y‖ at hcoord
      rw [Real.norm_eq_abs] at hcoord
      have hdist : Q ≤ ‖z - y‖ := by
        have ha := le_abs_self (9 / (N : ℝ) + Q - y i)
        have hlt : y i < 9 / (N : ℝ) := lt_of_not_ge hi
        linarith
      have hg := (coupledFunction_growth hN y).trans
        (mul_le_mul_of_nonneg_left (positiveDeficit_norm_le y z hz) (by norm_num : (0 : ℝ) ≤ 1 / 4))
      have hQid : (7 / 4 : ℝ) * Q = 4 * (M : ℝ) / N := by dsimp [Q]; field_simp; ring
      dsimp [sourcePayoff]
      nlinarith
  · exact chainMajorant_lower_bound hN z

theorem chainMajorant_infimum {M N : ℕ} (hN : 0 < N) :
    sInf (Set.range (chainMajorant (M := M) (N := N))) = -(4 * (M : ℝ) / N) := by
  have hb : BddBelow (Set.range (chainMajorant (M := M) (N := N))) := by
    refine ⟨-(4 * (M : ℝ) / N), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact chainMajorant_lower_bound hN x
  apply le_antisymm
  · have h := csInf_le hb (Set.mem_range_self (chainMinimizer M N))
    simpa only [chainMajorant_minimizer hN] using h
  · exact le_csInf (Set.range_nonempty _) (by
      rintro _ ⟨x, rfl⟩
      exact chainMajorant_lower_bound hN x)

/-- Proposition `prop:gap` / equation `newrand:exact-gap`. -/
theorem chainMajorant_gap {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    chainMajorant (0 : ChainSpace M N) - sInf (Set.range (chainMajorant (M := M) (N := N))) =
      (2 / (N : ℝ)) * (2 * (M : ℝ) + initialGamma M N) := by
  have hpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  rw [chainMajorant_zero hN, chainMajorant_infimum hpos, coupledFunction_zero hM hpos]
  ring

theorem chainMajorant_gap_le {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    chainMajorant (0 : ChainSpace M N) - sInf (Set.range (chainMajorant (M := M) (N := N))) ≤
      6 * (M : ℝ) / N := by
  rw [chainMajorant_gap hM hN]
  have hpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hgamma := (initialGamma_bounds hM hpos).2
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hg : initialGamma M N ≤ M := by linarith
  have h := mul_le_mul_of_nonneg_left (show 2 * (M : ℝ) + initialGamma M N ≤ 3 * M by linarith)
    (show 0 ≤ 2 / (N : ℝ) by positivity)
  convert h using 1 <;> first | rfl | ring

end WC
