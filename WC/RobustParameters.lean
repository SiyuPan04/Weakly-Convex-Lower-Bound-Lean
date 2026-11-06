import WC.ChainSources
import WC.Block

/-! Exact tolerance/intercept/flatness inequalities used by the robust source
locality proof. Coordinate ranks here are zero based. -/

noncomputable section
namespace WC

def robustTolerance (M N : ℕ) : ℝ := 1 / (64 * (N : ℝ) * ((M * N : ℕ) + 1))

theorem robustTolerance_pos (M : ℕ) {N : ℕ} (hN : 0 < N) : 0 < robustTolerance M N := by
  dsimp [robustTolerance]
  positivity

theorem tiltIntercept_unit_gap {K r s : ℕ} (hrs : r < s) :
    1 / (32 * ((K : ℝ) + 1)) ≤ tiltIntercept K r - tiltIntercept K s := by
  have hcast : (r : ℝ) + 1 ≤ s := by exact_mod_cast Nat.succ_le_of_lt hrs
  have hd : 0 < 32 * ((K : ℝ) + 1) := by positivity
  have heq : tiltIntercept K r - tiltIntercept K s =
      ((s : ℝ) - r) / (32 * ((K : ℝ) + 1)) := by dsimp [tiltIntercept]; ring
  rw [heq]
  exact (div_le_div_iff_of_pos_right hd).mpr (by linarith)

theorem robust_tilt_order {M N r s : ℕ} (hN : 0 < N) (hrs : r < s)
    {u v : ℝ} (hu : |u| ≤ robustTolerance M N) (hv : |v| ≤ robustTolerance M N) :
    7 / (256 * (((M * N : ℕ) : ℝ) + 1)) ≤
      (tiltIntercept (M * N) r - (N : ℝ) / 8 * u) -
        (tiltIntercept (M * N) s - (N : ℝ) / 8 * v) := by
  have hgap := tiltIntercept_unit_gap (K := M * N) hrs
  have hvar : u - v ≤ 2 * robustTolerance M N := by
    obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
    obtain ⟨hv₁, hv₂⟩ := abs_le.mp hv
    linarith
  have hm := mul_le_mul_of_nonneg_left hvar (by positivity : (0 : ℝ) ≤ (N : ℝ) / 8)
  have hnum : 1 / (32 * (((M * N : ℕ) : ℝ) + 1)) -
      (N : ℝ) / 8 * (2 * robustTolerance M N) =
      7 / (256 * (((M * N : ℕ) : ℝ) + 1)) := by
    dsimp [robustTolerance]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    push_cast
    field_simp
    ring
  linarith

theorem robust_tilt_order_strict {M N r s : ℕ} (hN : 0 < N) (hrs : r < s)
    {u v : ℝ} (hu : |u| ≤ robustTolerance M N) (hv : |v| ≤ robustTolerance M N) :
    tiltIntercept (M * N) s - (N : ℝ) / 8 * v <
      tiltIntercept (M * N) r - (N : ℝ) / 8 * u := by
  have h := robust_tilt_order hN hrs hu hv
  have hp : (0 : ℝ) < 7 / (256 * (((M * N : ℕ) : ℝ) + 1)) := by positivity
  linarith

theorem robustTolerance_progress_flat {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {u : ℝ} (hu : u ≤ robustTolerance M N) :
    (N : ℝ) / 4 * u - 1 / (64 * (N : ℝ)) ≤ 0 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ (M * N : ℕ) := by exact_mod_cast (Nat.le_mul_of_pos_left N hM)
  have hden : 0 < 64 * (N : ℝ) * (((M * N : ℕ) : ℝ) + 1) := by positivity
  have heta : robustTolerance M N ≤ 1 / (16 * (N : ℝ) ^ 2) := by
    dsimp [robustTolerance]
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * (N : ℝ) ^ 2)
    nlinarith
  have hbound : (N : ℝ) / 4 * (1 / (16 * (N : ℝ) ^ 2)) = 1 / (64 * (N : ℝ)) := by
    field_simp
    norm_num
  have hm := mul_le_mul_of_nonneg_left (hu.trans heta) (by positivity : (0 : ℝ) ≤ (N : ℝ) / 4)
  rw [hbound] at hm
  linarith

theorem hidden_progress_and_slope_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    {u : ℝ} (hu : u ≤ robustTolerance M N) :
    progressGate ((N : ℝ) / 4 * u - 1 / (64 * (N : ℝ))) = 0 ∧
    progressGateSlope ((N : ℝ) / 4 * u - 1 / (64 * (N : ℝ))) = 0 := by
  have hf := robustTolerance_progress_flat hM hN hu
  refine ⟨progressGate_of_nonpos hf, ?_⟩
  rw [progressGateSlope, if_pos hf]

end WC
