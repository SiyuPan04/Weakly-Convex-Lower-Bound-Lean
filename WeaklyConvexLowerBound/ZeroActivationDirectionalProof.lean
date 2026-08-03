import WeaklyConvexLowerBound.ZeroActivationFullFormula

/-!
# Directional domination at zero activation

This module closes the analytic premise isolated in
`ZeroActivationFullFormula`.  For a fixed ambient direction, each finite
tilted fan is represented by one active facet on a short one-sided segment.
The outer positive-part norm is then supported by the zero-score coordinates
at the base point.  Quadratic remainders vanish by
`linear_le_of_segment_quadratic`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set
open scoped BigOperators

/-- Reindex predecessor coefficients for an arbitrary scalar block field. -/
theorem sum_weight_mul_previousLinear {M : Nat} (hM : 0 < M)
    (w p : Fin M → ℝ) :
    (∑ m, w m * (if hm : m.1 = 0 then 0
      else p ⟨m.1 - 1, by omega⟩)) =
      ∑ m, nextOuterWeight w m * p m := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [nextOuterWeight]
  apply Finset.sum_congr rfl
  intro m _
  congr 2 <;> apply Fin.ext <;> simp

/-- A line in block space has the expected coordinate form. -/
@[simp] theorem blockLineAll_apply {M N : Nat}
    (z d : BlockVec M N) (t : ℝ) (m : Fin M) :
    (z + t • d) m = z m + t • d m := by
  rfl

/-- The score displacement along a block-space line has a uniform linear
bound.  The deliberately loose coefficient avoids square roots. -/
theorem sigmaScore_line_sub_le {M N : Nat} (hN : 0 < N)
    (z d : BlockVec M N) (m : Fin M) {t : ℝ} (ht : 0 ≤ t) :
    sigmaScore (z + t • d) m - sigmaScore z m ≤
      ((((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) * blockSq d) + 1) * t := by
  let B : ℝ := ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) * blockSq d
  have hK : 0 ≤ (N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32 := by positivity
  have hB : 0 ≤ B := mul_nonneg hK (blockSq_nonneg d)
  have hsq := sigmaScore_sub_sq_le_blockSq hN (z + t • d) z m
  have hsub : z + t • d - z = t • d := by
    ext i j
    simp
  rw [hsub, blockSq_smul_param] at hsq
  have hcoef :
      ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) *
          (t ^ 2 * blockSq d) = B * t ^ 2 := by
    dsimp [B]
    ring
  rw [hcoef] at hsq
  have hBL : B ≤ (B + 1) ^ 2 := by nlinarith [sq_nonneg B]
  have hsq' :
      (sigmaScore (z + t • d) m - sigmaScore z m) ^ 2 ≤
        ((B + 1) * t) ^ 2 := by
    calc
      _ ≤ B * t ^ 2 := hsq
      _ ≤ (B + 1) ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hBL (sq_nonneg t)
      _ = ((B + 1) * t) ^ 2 := by ring
  have hright : 0 ≤ (B + 1) * t := mul_nonneg (by linarith) ht
  have hmain :
      sigmaScore (z + t • d) m - sigmaScore z m ≤ (B + 1) * t := by
    nlinarith [sq_nonneg
      (sigmaScore (z + t • d) m - sigmaScore z m + (B + 1) * t)]
  simpa [B, add_assoc] using hmain

end

end WeaklyConvexLowerBound

