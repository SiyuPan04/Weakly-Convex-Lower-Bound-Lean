import WC.ChainBandBudget
import WC.SourceGrouping
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The manuscript's literal logarithmic band count, in addition to the
safe `3N` budget used for the final concrete family. -/

noncomputable section
namespace WC

def logarithmicBandCount (M N : ℕ) : ℕ :=
  ⌈Real.log (1024 * (M : ℝ) / Real.sqrt (N : ℝ)) / Real.log 8⌉₊

theorem logarithmicBandCount_cover {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    1024 * (M : ℝ) / Real.sqrt (N : ℝ) ≤ (8 : ℝ) ^ logarithmicBandCount M N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < 1024 * (M : ℝ) / Real.sqrt (N : ℝ) := by positivity
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log (1024 * (M : ℝ) / Real.sqrt (N : ℝ)) / Real.log 8)
  have hlog : Real.log (1024 * (M : ℝ) / Real.sqrt (N : ℝ)) ≤
      (logarithmicBandCount M N : ℝ) * Real.log 8 := (div_le_iff₀ h8).mp hc
  have hh := (Real.log_le_iff_le_exp hx).mp hlog
  rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh

theorem logarithmicBandCount_le_threeN {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) : logarithmicBandCount M N ≤ 3 * N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast (show 1 ≤ N by omega)
  have hx : 0 < 1024 * (M : ℝ) / Real.sqrt (N : ℝ) := by positivity
  have hm : (M : ℝ) ≤ (2 : ℝ) ^ (8 * N) := by exact_mod_cast hMmax
  have hp : (2 : ℝ) ^ (10 + 8 * N) ≤ (2 : ℝ) ^ (9 * N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow : 1024 * (M : ℝ) / Real.sqrt (N : ℝ) ≤ (8 : ℝ) ^ (3 * N) := by
    calc
      _ ≤ 1024 * (M : ℝ) := div_le_self (by positivity) hs1
      _ ≤ (2 : ℝ) ^ 10 * (2 : ℝ) ^ (8 * N) := by norm_num; linarith
      _ = (2 : ℝ) ^ (10 + 8 * N) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ) ^ (9 * N) := hp
      _ = (8 : ℝ) ^ (3 * N) := by
        rw [show 9 * N = 3 * (3 * N) by omega, pow_mul]
        norm_num
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 8))).mpr
  simpa only [Real.log_pow] using Real.log_le_log hx hpow

theorem chain_source_radius_logarithmic_coverage {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    chainSourceRadius M N ≤ (8 : ℝ) ^ logarithmicBandCount M N * chainNearRadius N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hc := positiveScoreTerm_lipschitzConstant_le hN
  let c : ℝ := 1 / 4 + 3 / (2 * Real.sqrt (N : ℝ))
  have hden : 0 < 2 - c := by dsimp [c]; linarith
  have hsimple : chainSourceRadius M N ≤ 1024 * (M : ℝ) / (288 * (N : ℝ)) := by
    unfold chainSourceRadius
    apply (div_le_div_iff₀ (mul_pos hNR hden) (by positivity : 0 < 288 * (N : ℝ))).mpr
    have hcoef : (1152 : ℝ) ≤ 1024 * (2 - c) := by dsimp [c]; linarith
    have hscale := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (M : ℝ) * N by positivity)
    nlinarith
  have hid : 1024 * (M : ℝ) / (288 * (N : ℝ)) =
      (1024 * (M : ℝ) / Real.sqrt (N : ℝ)) * chainNearRadius N := by
    unfold chainNearRadius
    field_simp
    nlinarith [Real.sq_sqrt hNR.le]
  rw [hid] at hsimple
  exact hsimple.trans (mul_le_mul_of_nonneg_right
    (logarithmicBandCount_cover hM (by omega)) (chainNearRadius_pos (by omega)).le)

end WC
