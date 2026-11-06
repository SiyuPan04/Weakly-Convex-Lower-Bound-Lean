import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

/-! Exact logarithmic dimension and probability budget in the MP reduction. -/

namespace MP
open scoped ENNReal

def logarithmicDimensionBound (K T d : ℕ) (R η δ : ℝ) : Prop :=
  (K : ℝ) + 1 + (128 * R ^ 2 / (9 * η ^ 2)) *
    Real.log (2 * (K : ℝ) * (T + 1) / δ) ≤ d

theorem logarithmic_dimension_positive {K T d : ℕ} {R η δ : ℝ}
    (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hd : logarithmicDimensionBound K T d R η δ) : K + 1 ≤ d := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht : (0 : ℝ) ≤ T := by positivity
  have hq : 1 ≤ 2 * (K : ℝ) * (T + 1) / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hl : 0 ≤ Real.log (2 * (K : ℝ) * (T + 1) / δ) := Real.log_nonneg hq
  have ha : 0 ≤ 128 * R ^ 2 / (9 * η ^ 2) := by positivity
  have hp := mul_nonneg ha hl
  unfold logarithmicDimensionBound at hd
  have hd' : (K : ℝ) + 1 ≤ d := by linarith
  exact_mod_cast hd'

theorem logarithmic_dimension_budget {K T d : ℕ} {R η δ : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hη : 0 < η) (hδ : 0 < δ)
    (hd : logarithmicDimensionBound K T d R η δ) :
    (K : ℝ) * (T + 1) *
      (2 * Real.exp (-(9 * ((d : ℝ) - K) * η ^ 2) / (128 * R ^ 2))) ≤ δ := by
  let Q : ℝ := 2 * (K : ℝ) * (T + 1)
  let a : ℝ := 128 * R ^ 2 / (9 * η ^ 2)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog : Real.log (Q / δ) ≤ ((d : ℝ) - K) / a := by
    apply (le_div_iff₀ ha).mpr
    change (K : ℝ) + 1 + a * Real.log (Q / δ) ≤ d at hd
    nlinarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hlog)
  rw [show Real.exp (-Real.log (Q / δ)) = (Q / δ)⁻¹ by
    rw [Real.exp_neg, Real.exp_log (div_pos hQ hδ)]] at he
  have halg : -(9 * ((d : ℝ) - K) * η ^ 2) / (128 * R ^ 2) = -(((d : ℝ) - K) / a) := by
    dsimp [a]
    field_simp
  rw [halg]
  have hmul := mul_le_mul_of_nonneg_left he hQ.le
  have hid : Q * (Q / δ)⁻¹ = δ := by field_simp
  rw [hid] at hmul
  dsimp [Q] at hmul
  nlinarith

theorem logarithmic_dimension_budget_ennreal {K T d : ℕ} {R η δ : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hη : 0 < η) (hδ : 0 < δ)
    (hd : logarithmicDimensionBound K T d R η δ) :
    (((T + 1) * K : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (2 * Real.exp (-(9 * ((d : ℝ) - K) * η ^ 2) / (128 * R ^ 2))) ≤
      ENNReal.ofReal δ := by
  have hc : (((T + 1) * K : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) * (T + 1)) := by
    have heq : (K : ℝ) * (T + 1) = (((T + 1) * K : ℕ) : ℝ) := by push_cast; ring
    rw [heq, ENNReal.ofReal_natCast]
  rw [hc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K : ℝ) * (T + 1))]
  exact ENNReal.ofReal_le_ofReal (logarithmic_dimension_budget hK hR hη hδ hd)

end MP
