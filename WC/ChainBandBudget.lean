import WC.RawLipschitz
import Mathlib.Tactic.FieldSimp

/-! A uniform finite geometric-band budget.  The maximum `3N` budget is
allowed in the source grouping argument, avoiding a logarithmic roundoff
in the concrete family while retaining the manuscript's constants. -/

noncomputable section
namespace WC

theorem chain_source_radius_nonneg (M N : ℕ) (hN : 256 ≤ N) :
    0 ≤ chainSourceRadius M N := by
  have hc := positiveScoreTerm_lipschitzConstant_le hN
  have hden : 0 < 2 - (1 / 4 + 3 / (2 * Real.sqrt (N : ℝ))) := by linarith
  unfold chainSourceRadius
  positivity

theorem chain_source_radius_threeN_coverage {M N : ℕ} (hN : 256 ≤ N)
    (hM : M ≤ 2 ^ (8 * N)) :
    chainSourceRadius M N ≤ (8 : ℝ) ^ (3 * N) / (288 * Real.sqrt (N : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast (show 1 ≤ N by omega)
  have hc := positiveScoreTerm_lipschitzConstant_le hN
  let c : ℝ := 1 / 4 + 3 / (2 * Real.sqrt (N : ℝ))
  have hden : 0 < 2 - c := by dsimp [c]; linarith
  have hMreal : (M : ℝ) ≤ (2 : ℝ) ^ (8 * N) := by exact_mod_cast hM
  have hp : (2 : ℝ) ^ (10 + 8 * N) ≤ (2 : ℝ) ^ (9 * N) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hpow : (1024 : ℝ) * M ≤ (8 : ℝ) ^ (3 * N) := by
    calc
      (1024 : ℝ) * M ≤ (2 : ℝ) ^ 10 * (2 : ℝ) ^ (8 * N) := by
        norm_num
        linarith
      _ = (2 : ℝ) ^ (10 + 8 * N) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ) ^ (9 * N) := hp
      _ = (8 : ℝ) ^ (3 * N) := by
        have heq : 9 * N = 3 * (3 * N) := by omega
        rw [heq, pow_mul]
        norm_num
  have hcore : (1152 : ℝ) * M ≤ (1024 : ℝ) * M * (2 - c) * Real.sqrt (N : ℝ) := by
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hc' : (1152 : ℝ) ≤ 1024 * (2 - c) := by dsimp [c]; linarith
    have h1 := mul_le_mul_of_nonneg_right hc' hM0
    have h2 := mul_le_mul_of_nonneg_left hs1
      (show 0 ≤ 1024 * (M : ℝ) * (2 - c) by positivity)
    nlinarith
  have hfinal : (1152 : ℝ) * M ≤ (8 : ℝ) ^ (3 * N) * (2 - c) * Real.sqrt (N : ℝ) := by
    apply hcore.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hden.le) hs.le
  unfold chainSourceRadius
  apply (div_le_div_iff₀ (mul_pos hNR hden) (mul_pos (by norm_num) hs)).mpr
  change 4 * (M : ℝ) * (288 * Real.sqrt (N : ℝ)) ≤
    (8 : ℝ) ^ (3 * N) * ((N : ℝ) * (2 - c))
  have hmul := mul_le_mul_of_nonneg_right hfinal hs.le
  rw [mul_assoc ((8 : ℝ) ^ (3 * N) * (2 - c)), Real.mul_self_sqrt hNR.le] at hmul
  nlinarith

end WC
