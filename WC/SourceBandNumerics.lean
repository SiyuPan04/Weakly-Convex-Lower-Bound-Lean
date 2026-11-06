import WC.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact numerical separation in the source-band exchange argument. -/

namespace WC

theorem source_band_phi_margin {q : ℝ} (hq0 : 1 ≤ q) (hq8 : q ≤ 8) :
    (11 / 32 : ℝ) < 1 + q - Real.sqrt (1 + q ^ 2 - q / 32) - Real.sqrt (q / 32) := by
  have hqpos : 0 ≤ q := by linarith
  have hA0 := Real.sqrt_nonneg (1 + q ^ 2 - q / 32)
  have hB0 := Real.sqrt_nonneg (q / 32)
  have hinside : 0 ≤ 1 + q ^ 2 - q / 32 := by nlinarith [sq_nonneg (q - 1)]
  have hA2 := Real.sq_sqrt hinside
  have hB2 := Real.sq_sqrt (show 0 ≤ q / 32 by positivity)
  by_cases hq2 : q ≤ 2
  · have hboundpos : 0 ≤ q - 1 + 45 / 32 := by linarith
    have hsq : (Real.sqrt (1 + q ^ 2 - q / 32)) ^ 2 < (q - 1 + 45 / 32) ^ 2 := by
      nlinarith
    have hA : Real.sqrt (1 + q ^ 2 - q / 32) < q - 1 + 45 / 32 := by nlinarith
    have hB : Real.sqrt (q / 32) ≤ 1 / 4 := by nlinarith
    linarith
  · have hq2' : 2 ≤ q := le_of_lt (lt_of_not_ge hq2)
    by_cases hq4 : q ≤ 4
    · have hA : Real.sqrt (1 + q ^ 2 - q / 32) ≤ q + 1 / 4 := by
        have hsq : (Real.sqrt (1 + q ^ 2 - q / 32)) ^ 2 ≤ (q + 1 / 4) ^ 2 := by nlinarith
        nlinarith
      have hB : Real.sqrt (q / 32) ≤ 3 / 8 := by nlinarith
      linarith
    · have hq4' : 4 ≤ q := le_of_lt (lt_of_not_ge hq4)
      have hA : Real.sqrt (1 + q ^ 2 - q / 32) ≤ q + 1 / 8 := by
        have hsq : (Real.sqrt (1 + q ^ 2 - q / 32)) ^ 2 ≤ (q + 1 / 8) ^ 2 := by nlinarith
        nlinarith
      have hB : Real.sqrt (q / 32) ≤ 1 / 2 := by nlinarith
      linarith

/-- Moving mass toward the diagonal increases the sum of two square roots. -/
theorem two_norms_sum_le {u v A B : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B)
    (hvB : v ≤ B) (hBA : B ≤ A) (hvu : v ≤ u)
    (hsq : u ^ 2 + v ^ 2 = A ^ 2 + B ^ 2) : u + v ≤ A + B := by
  by_contra h
  have hd : 0 < (u - A) - (B - v) := by linarith
  have hsum : 0 < u + A := by linarith
  have hprod := mul_pos hd hsum
  have hother := mul_nonneg (sub_nonneg.mpr hvB) (show 0 ≤ u + A - B - v by linarith)
  nlinarith

theorem source_band_normalized_contradiction {q u v : ℝ}
    (hq0 : 1 ≤ q) (hq8 : q ≤ 8) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvu : v ≤ u) (hsq : u ^ 2 + v ^ 2 = 1 + q ^ 2)
    (hvsmall : v ^ 2 ≤ q / 32) : (11 / 32 : ℝ) < 1 + q - u - v := by
  let A := Real.sqrt (1 + q ^ 2 - q / 32)
  let B := Real.sqrt (q / 32)
  have hq : 0 ≤ q := by linarith
  have hins : 0 < 1 + q ^ 2 - q / 32 := by nlinarith [sq_nonneg (q - 1)]
  have hA2 : A ^ 2 = 1 + q ^ 2 - q / 32 := Real.sq_sqrt hins.le
  have hB2 : B ^ 2 = q / 32 := Real.sq_sqrt (by positivity)
  have hA : 0 < A := Real.sqrt_pos.mpr hins
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hvB : v ≤ B := by nlinarith
  have hBA : B ≤ A := by nlinarith [sq_nonneg (q - 1)]
  have hsum := two_norms_sum_le hu hv hA hB hvB hBA hvu (by linarith)
  have hmargin := source_band_phi_margin hq0 hq8
  dsimp [A, B] at hsum
  linarith

end WC
