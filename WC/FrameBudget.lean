import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The exact ambient-dimension budget in the randomized rotation theorem. -/

namespace WC

theorem rotation_dimension_budget {K T d : ℕ} {B η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ)
    (hd : K + 2 + ⌈4 * (K : ℝ) * (T + 1) * B ^ 2 / (δ * η ^ 2)⌉₊ ≤ d) :
    (K : ℝ) * (T + 1) * (4 * B ^ 2 / (((d : ℝ) - K) * η ^ 2)) ≤ δ := by
  let q : ℝ := 4 * (K : ℝ) * (T + 1) * B ^ 2 / (δ * η ^ 2)
  have hceil : q ≤ (⌈q⌉₊ : ℝ) := Nat.le_ceil q
  have hceil0 : (0 : ℝ) ≤ (⌈q⌉₊ : ℝ) := Nat.cast_nonneg _
  have hdreal : (K : ℝ) + 2 + (⌈q⌉₊ : ℝ) ≤ d := by
    dsimp [q]
    exact_mod_cast hd
  have hD : 0 < (d : ℝ) - K := by linarith
  have hqD : q ≤ (d : ℝ) - K := by linarith
  have hden : 0 < δ * η ^ 2 := mul_pos hδ (sq_pos_of_pos hη)
  have hmass : 4 * (K : ℝ) * (T + 1) * B ^ 2 ≤
      ((d : ℝ) - K) * (δ * η ^ 2) := (div_le_iff₀ hden).1 hqD
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hD (sq_pos_of_pos hη))).2
  nlinarith

theorem rotation_dimension_budget_ennreal {K T d : ℕ} {B η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ)
    (hd : K + 2 + ⌈4 * (K : ℝ) * (T + 1) * B ^ 2 / (δ * η ^ 2)⌉₊ ≤ d) :
    ENNReal.ofReal ((K : ℝ) * (T + 1)) *
      ENNReal.ofReal (4 * B ^ 2 / (((d : ℝ) - K) * η ^ 2)) ≤ ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K : ℝ) * (T + 1))]
  exact ENNReal.ofReal_le_ofReal (rotation_dimension_budget hη hδ hd)

end WC
