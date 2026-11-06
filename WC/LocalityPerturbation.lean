import WC.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp

/-! A norm-preserving front perturbation has a strict objective gain whenever
the score radius is below the front-curvature threshold. No second derivative
or Taylor expansion is assumed. -/

namespace WC
open Filter Topology

theorem exists_sqrt_perturbation {S R A B C ε : ℝ}
    (hS : 0 < S) (hR : 0 < R) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hratio : B * S < A * R) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      B * (Real.sqrt (R ^ 2 + C * t ^ 2) - R) <
        Real.sqrt (S ^ 2 + A * C * t ^ 2) - S := by
  let D : ℝ → ℝ := fun t => A * (Real.sqrt (R ^ 2 + C * t ^ 2) + R) -
    B * (Real.sqrt (S ^ 2 + A * C * t ^ 2) + S)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hD0 : 0 < D 0 := by
    simp only [D, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      Real.sqrt_sq hR.le, Real.sqrt_sq hS.le]
    nlinarith
  have hev := hD.continuousAt.eventually (lt_mem_nhds hD0)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let t := min ε δ / 2
  have ht : 0 < t := by dsimp [t]; exact div_pos (lt_min hε hδ) (by norm_num)
  have htε : t < ε := by
    have hmin := min_le_left ε δ
    dsimp [t]
    linarith
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    have hmin := min_le_right ε δ
    dsimp [t]
    linarith
  have hDt := hnear htδ
  let U := Real.sqrt (S ^ 2 + A * C * t ^ 2)
  let V := Real.sqrt (R ^ 2 + C * t ^ 2)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hU2 : U ^ 2 = S ^ 2 + A * C * t ^ 2 := Real.sq_sqrt (by positivity)
  have hV2 : V ^ 2 = R ^ 2 + C * t ^ 2 := Real.sq_sqrt (by positivity)
  have hUS : 0 < U + S := by linarith
  have hVR : 0 < V + R := by linarith
  have hUd : (U - S) * (U + S) = A * C * t ^ 2 := by nlinarith
  have hVd : (V - R) * (V + R) = C * t ^ 2 := by nlinarith
  change 0 < A * (V + R) - B * (U + S) at hDt
  have hmul := mul_lt_mul_of_pos_left (show B * (U + S) < A * (V + R) by linarith)
    (show 0 < C * t ^ 2 by positivity)
  have hleft : (B * (V - R)) * ((U + S) * (V + R)) =
      (C * t ^ 2) * (B * (U + S)) := by
    calc
      _ = B * (U + S) * ((V - R) * (V + R)) := by ring
      _ = _ := by rw [hVd]; ring
  have hright : (U - S) * ((U + S) * (V + R)) =
      (C * t ^ 2) * (A * (V + R)) := by
    calc
      _ = ((U - S) * (U + S)) * (V + R) := by ring
      _ = _ := by rw [hUd]; ring
  have hgain : B * (V - R) < U - S := by
    apply (mul_lt_mul_iff_left₀ (mul_pos hUS hVR)).mp
    rw [hleft, hright]
    exact hmul
  exact ⟨t, ht, htε, hgain⟩

theorem exists_front_objective_gain {N S R C ε : ℝ}
    (hN : 0 < N) (hS : 0 < S) (hR : 0 < R) (hC : 0 < C)
    (hfront : 64 * S < N * R) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      2 * (Real.sqrt (R ^ 2 + C * t ^ 2) - R) <
        (2 / N) * (Real.sqrt (S ^ 2 + (N ^ 2 / 64) * C * t ^ 2) - S) := by
  have hratio : N * S < (N ^ 2 / 64) * R := by
    have hm := mul_lt_mul_of_pos_left hfront hN
    nlinarith
  obtain ⟨t, ht, htε, hg⟩ := exists_sqrt_perturbation hS hR
    (by positivity : 0 < N ^ 2 / 64) hN hC hratio hε
  refine ⟨t, ht, htε, ?_⟩
  have hm := mul_lt_mul_of_pos_left hg (show 0 < 2 / N by positivity)
  have heq : (2 / N) * (N * (Real.sqrt (R ^ 2 + C * t ^ 2) - R)) =
      2 * (Real.sqrt (R ^ 2 + C * t ^ 2) - R) := by field_simp
  rwa [heq] at hm

end WC
