import WCLB.Model
import WCLB.UniformFamily

/-! `thm:main` of the WCLB manuscript with the explicit constants used
in its scaling proof. The imported normalized families are constructed
and proved, rather than assumed as a certificate. -/

noncomputable section
namespace WCLB

theorem small_accuracy_ratios {G ρ Δ ε : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (haccuracy : ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ))) :
    (2 : ℝ) ^ 18 ≤ G ^ 2 / ε ^ 2 ∧
      (2 : ℝ) ^ 18 ≤ ρ * Δ / ε ^ 2 := by
  have hGacc : ε ≤ (1 / 512 : ℝ) * G :=
    haccuracy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hSacc : ε ≤ (1 / 512 : ℝ) * Real.sqrt (ρ * Δ) :=
    haccuracy.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
  have hGs : (512 * ε) ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 512 * ε) hG.le).mpr (by linarith)
  have hSs : (512 * ε) ^ 2 ≤ Real.sqrt (ρ * Δ) ^ 2 :=
    (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 512 * ε) (Real.sqrt_nonneg _)).mpr (by linarith)
  rw [Real.sq_sqrt (mul_pos hρ hΔ).le] at hSs
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    norm_num
    nlinarith
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    norm_num
    nlinarith

/-- The explicit lower bound proved in the manuscript: `c₀=1/512`
and `c=2⁻²⁹`, uniformly over every confidence `ν∈[0,1)`. -/
theorem main_explicit {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (haccuracy : ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ)))
    (hgap : Δ ≤ (G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2)))
    (hν : 0 ≤ ν) (hν_one : ν < 1) :
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      WC.Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  obtain ⟨hb, hs⟩ := small_accuracy_ratios hG hρ hΔ hε haccuracy
  have hgap' : Δ ≤ (G ^ 2 / ρ) * Real.exp ((G ^ 2 / ε ^ 2) / 200) := by
    have heq : (G ^ 2 / ε ^ 2) / 200 = G ^ 2 / (200 * ε ^ 2) := by ring
    rwa [heq]
  exact WC.LowerReduction.scaling_reduction WCLB.uniformFamilies
    hG hρ hΔ hε hν hν_one hb hs hgap'

theorem main : Model.MainTheorem := by
  refine ⟨1 / 512, 1 / (2 : ℝ) ^ 29, by norm_num, by positivity, ?_⟩
  intro G ρ Δ ε ν hG hρ hΔ hε haccuracy hgap hν hν_one
  exact main_explicit hG hρ hΔ hε haccuracy hgap hν hν_one

end WCLB
