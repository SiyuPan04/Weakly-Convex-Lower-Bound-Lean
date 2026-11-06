import WC.TerminalActivation

/-! Quantitative separation of a small-coordinate query from the actual raw minimizers. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem terminalRegion_coordinate_ge {M N : ℕ} (hN : 0 < N) {z : ChainSpace M N}
    (hz : z ∈ terminalRegion) (i : Fin M × Fin N) : 6 / (N : ℝ) ≤ z i := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrank : i.1.val * N + i.2.val < M * N := by
    calc
      _ < i.1.val * N + N := Nat.add_lt_add_left i.2.isLt _
      _ = (i.1.val + 1) * N := by ring
      _ ≤ M * N := Nat.mul_le_mul_right N i.1.isLt
  have hc := tiltIntercept_gt_one hrank
  have hp := hz i.1 i.2
  dsimp [fanPiece, coupledBlock] at hp
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem terminalRegion_nonempty {M N : ℕ} (hN : 0 < N) :
    (terminalRegion (M := M) (N := N)).Nonempty :=
  ⟨constantCompletion M N, (coupledFunction_eq_minimum_iff_terminalRegion hN _).mp
    (coupledFunction_completion hN)⟩

theorem norm_sub_terminalRegion_lower {M N : ℕ} (hN : 0 < N) {η : ℝ}
    (hη : η ≤ 6 / (N : ℝ)) (x z : ChainSpace M N) (hz : z ∈ terminalRegion)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card) (hsmall : ∀ i ∈ s, x i ≤ η) :
    (6 / (N : ℝ) - η) * Real.sqrt (N : ℝ) ≤ ‖x - z‖ := by
  let gap : ℝ := 6 / (N : ℝ) - η
  have hgap : 0 ≤ gap := sub_nonneg.mpr hη
  have hcoord (i : Fin M × Fin N) (hi : i ∈ s) : gap ^ 2 ≤ (x i - z i) ^ 2 := by
    have hzcoord := terminalRegion_coordinate_ge hN hz i
    have hxcoord := hsmall i hi
    have ha : gap ≤ |x i - z i| := by
      have h := neg_le_abs (x i - z i)
      dsimp [gap]
      linarith
    have h := (sq_le_sq₀ hgap (abs_nonneg (x i - z i))).mpr ha
    simpa only [sq_abs] using h
  have hsum : (N : ℝ) * gap ^ 2 ≤ ∑ i ∈ s, (x i - z i) ^ 2 := by
    calc
      _ ≤ (s.card : ℝ) * gap ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg gap)
      _ = ∑ _i ∈ s, gap ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum hcoord
  have htotal : (∑ i ∈ s, (x i - z i) ^ 2) ≤ ‖x - z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    exact sq_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hgap (Real.sqrt_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)]
  calc
    gap ^ 2 * (N : ℝ) = (N : ℝ) * gap ^ 2 := mul_comm _ _
    _ ≤ _ := hsum
    _ ≤ _ := htotal

end WC
