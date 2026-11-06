import WC.ScoreLipschitz
import WC.MajorantSources
import WC.SourceOrthant

/-! The actual least 2-Lipschitz majorant of the coupled hard instance. -/

noncomputable section
namespace WC
open scoped BigOperators

def chainMajorant {M N : ℕ} (x : ChainSpace M N) : ℝ :=
  lipschitzMajorant coupledFunction 2 x

theorem positiveDeficit_norm_le {M N : ℕ} (y z : ChainSpace M N)
    (hz : ∀ i, 9 / (N : ℝ) ≤ z i) : ‖positiveDeficit y‖ ≤ ‖z - y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hm : max (9 / (N : ℝ) - y i) 0 ≤ |z i - y i| := by
    apply max_le
    · exact (sub_le_sub_right (hz i) _).trans (le_abs_self _)
    · exact abs_nonneg _
  have h := (sq_le_sq₀ (le_max_right (9 / (N : ℝ) - y i) 0) (abs_nonneg (z i - y i))).mpr hm
  simpa only [positiveDeficit, PiLp.toLp_apply, PiLp.sub_apply, sq_abs] using h

theorem coupledFunction_subcritical_growth {M N : ℕ} (hN : 0 < N) (y : ChainSpace M N) :
    coupledFunction y ≤ (1 / 4 : ℝ) * ‖constantCompletion M N - y‖ :=
  (coupledFunction_growth hN y).trans (mul_le_mul_of_nonneg_left
    (positiveDeficit_norm_le y (constantCompletion M N) (fun _ => le_rfl)) (by norm_num))

theorem chainMajorant_finite {M N : ℕ} (hN : 0 < N) :
    MajorantFinite (coupledFunction (M := M) (N := N)) 2 :=
  majorant_finite_of_growth (A := 0) (constantCompletion M N) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 2) (by
      intro y
      simpa only [zero_add] using coupledFunction_subcritical_growth hN y)

theorem chainMajorant_lipschitz {M N : ℕ} (hN : 0 < N) :
    GloballyLipschitz 2 (chainMajorant (M := M) (N := N)) :=
  majorant_lipschitz (by norm_num) (chainMajorant_finite hN)

theorem chainMajorant_weaklyConvex {M N : ℕ} (hN : 0 < N) :
    WeaklyConvex (9 / 2 : ℝ) (chainMajorant (M := M) (N := N)) :=
  majorant_weaklyConvex (chainMajorant_finite hN) (weaklyConvex_coupledFunction hN)

theorem chainMajorant_continuous {M N : ℕ} (hN : 0 < N) :
    Continuous (chainMajorant (M := M) (N := N)) :=
  WC.GloballyLipschitz.continuous (by norm_num) (chainMajorant_lipschitz hN)

theorem coupledFunction_le_chainMajorant {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    coupledFunction x ≤ chainMajorant x := le_lipschitzMajorant (chainMajorant_finite hN) x

theorem chainMajorant_lower_bound {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    -(4 * (M : ℝ) / N) ≤ chainMajorant x :=
  (coupledFunction_lower_bound hN x).trans (coupledFunction_le_chainMajorant hN x)

theorem chainMajorant_sources_nonempty {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    (majorantSources coupledFunction 2 x).Nonempty :=
  majorantSources_nonempty (A := 0) (constantCompletion M N) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 2) (continuous_coupledFunction hN)
    (by intro y; simpa only [zero_add] using coupledFunction_subcritical_growth hN y) x

theorem chainMajorant_sources_isCompact {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    IsCompact (majorantSources coupledFunction 2 x) :=
  majorantSources_isCompact (A := 0) (constantCompletion M N) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 2) (continuous_coupledFunction hN)
    (by intro y; simpa only [zero_add] using coupledFunction_subcritical_growth hN y) x

end WC
