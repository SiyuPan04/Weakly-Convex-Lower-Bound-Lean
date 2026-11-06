import WC.AuxiliaryLowerReduction
import WC.UpperModel

/-! The boundary constructions close every parameter regime. The sole
construction-dependent premise here is the main large-chain family. -/

noncomputable section
open scoped ENNReal
namespace WC
namespace BoundaryLower

def universalLowerConstant : ℝ :=
  1 / ((2 : ℝ) ^ 40 * Real.exp ((2 : ℝ) ^ 18 / 200))

theorem universalLowerConstant_pos : 0 < universalLowerConstant := by
  unfold universalLowerConstant
  positivity

theorem universalLowerConstant_le : universalLowerConstant ≤ 1 / (2 : ℝ) ^ 40 := by
  have he : 1 ≤ Real.exp ((2 : ℝ) ^ 18 / 200) := Real.one_le_exp_iff.mpr (by positivity)
  unfold universalLowerConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem principal_lower_bound (families : LowerReduction.UniformFamilies)
    {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (hν : 0 ≤ ν) (hν_one : ν < 1) (hgap : ε ^ 2 ≤ ρ * Δ)
    (hgap_range : Δ ≤ (G ^ 2 / ρ) * Real.exp ((G ^ 2 / ε ^ 2) / 200)) :
    ENNReal.ofReal (universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  let b := G ^ 2 / ε ^ 2
  let s := ρ * Δ / ε ^ 2
  have hb : 0 < b := div_pos (sq_pos_of_pos hG) (sq_pos_of_pos hε)
  have hρΔ : 0 < ρ * Δ := (sq_pos_of_pos hε).trans_le hgap
  have hΔ : 0 < Δ := (mul_pos_iff_of_pos_left hρ).mp hρΔ
  have hs : 0 < s := div_pos hρΔ (sq_pos_of_pos hε)
  have hid : ρ * G ^ 2 * Δ / ε ^ 4 = b * s := by dsimp [b, s]; field_simp
  have htarget : 0 ≤ ρ * G ^ 2 * Δ / ε ^ 4 := by positivity
  have hc := universalLowerConstant_pos
  by_cases hbsmall : b < (2 : ℝ) ^ 18
  · have hsupper : s ≤ b * Real.exp (b / 200) := by
      apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
      calc
        ρ * Δ ≤ ρ * ((G ^ 2 / ρ) * Real.exp (b / 200)) :=
          mul_le_mul_of_nonneg_left hgap_range hρ.le
        _ = (b * Real.exp (b / 200)) * ε ^ 2 := by dsimp [b]; field_simp
    have hprod : b * s ≤ (2 : ℝ) ^ 40 * Real.exp ((2 : ℝ) ^ 18 / 200) := by
      calc
        b * s ≤ b * (b * Real.exp (b / 200)) := mul_le_mul_of_nonneg_left hsupper hb.le
        _ = b ^ 2 * Real.exp (b / 200) := by ring
        _ ≤ ((2 : ℝ) ^ 18) ^ 2 * Real.exp ((2 : ℝ) ^ 18 / 200) := by
          apply mul_le_mul
          · exact (sq_le_sq₀ hb.le (by positivity)).mpr hbsmall.le
          · exact Real.exp_le_exp.mpr (by linarith)
          · exact (Real.exp_pos _).le
          · positivity
        _ ≤ (2 : ℝ) ^ 40 * Real.exp ((2 : ℝ) ^ 18 / 200) := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    have hctarget : universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 ≤ 1 := by
      have heq : universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 =
          (b * s) / ((2 : ℝ) ^ 40 * Real.exp ((2 : ℝ) ^ 18 / 200)) := by
        rw [show universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 =
          universalLowerConstant * (ρ * G ^ 2 * Δ / ε ^ 4) by ring, hid]
        unfold universalLowerConstant
        ring
      rw [heq]
      exact (div_le_one (by positivity)).mpr hprod
    calc
      ENNReal.ofReal (universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4) ≤ 1 :=
        (ENNReal.ofReal_le_ofReal hctarget).trans_eq (by norm_num)
      _ ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le :=
        zero_call_lower_bound hG hρ hε hεG
          ((div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hgap)) hν_one
  have hblarge : (2 : ℝ) ^ 18 ≤ b := le_of_not_gt hbsmall
  by_cases hssmall : s < (2 : ℝ) ^ 18
  · have hcsmall : universalLowerConstant * (2 : ℝ) ^ 18 ≤ 1 / 160 := by
      have hh := mul_le_mul_of_nonneg_right universalLowerConstant_le (by positivity : 0 ≤ (2 : ℝ) ^ 18)
      norm_num at hh
      linarith
    have hcs : universalLowerConstant * s ≤ 1 / 160 :=
      (mul_le_mul_of_nonneg_left hssmall.le hc.le).trans hcsmall
    have hctarget : universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 ≤ b / 160 := by
      calc
        universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 = universalLowerConstant * (b * s) := by rw [← hid]; ring
        _ = (universalLowerConstant * s) * b := by ring
        _ ≤ (1 / 160) * b := mul_le_mul_of_nonneg_right hcs hb.le
        _ = b / 160 := by ring
    exact (ENNReal.ofReal_le_ofReal hctarget).trans
      (auxiliary_lower_bound hG hρ hε hν hν_one (by dsimp [b] at hblarge; norm_num at hblarge; linarith) hgap)
  · have hclarge : universalLowerConstant ≤ 1 / (2 : ℝ) ^ 29 :=
      universalLowerConstant_le.trans (by norm_num)
    have hctarget : universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 ≤
        (1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4 := by
      calc
        universalLowerConstant * ρ * G ^ 2 * Δ / ε ^ 4 =
            universalLowerConstant * (ρ * G ^ 2 * Δ / ε ^ 4) := by ring
        _ ≤ (1 / (2 : ℝ) ^ 29) * (ρ * G ^ 2 * Δ / ε ^ 4) :=
          mul_le_mul_of_nonneg_right hclarge htarget
        _ = (1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4 := by ring
    exact (ENNReal.ofReal_le_ofReal hctarget).trans
      (LowerReduction.scaling_reduction families hG hρ hΔ hε hν hν_one hblarge
        (le_of_not_gt hssmall) hgap_range)

/-- All parameter reductions and the actual upper algorithm are complete.
Only the concrete large-chain family is supplied by the construction modules. -/
theorem mainTheorem_of_uniformFamilies (families : LowerReduction.UniformFamilies) : Model.MainTheorem := by
  refine ⟨universalLowerConstant, 540705, universalLowerConstant_pos, by norm_num, ?_⟩
  intro G ρ Δ ε ν hG hρ hν hν_one hε hrange hgap_range
  have hεG : ε < G := hrange.trans_le (min_le_left _ _)
  have hεsqrt : ε < Real.sqrt (ρ * Δ) := hrange.trans_le (min_le_right _ _)
  have hρΔ : 0 ≤ ρ * Δ := (Real.sqrt_pos.mp (hε.trans hεsqrt)).le
  have hgap : ε ^ 2 ≤ ρ * Δ := by
    have hs := Real.sq_sqrt hρΔ
    nlinarith [Real.sqrt_nonneg (ρ * Δ)]
  have hGε : ε ^ 2 ≤ G ^ 2 := by nlinarith
  have hex : G ^ 2 / (200 * ε ^ 2) = (G ^ 2 / ε ^ 2) / 200 := by field_simp
  rw [hex] at hgap_range
  exact ⟨principal_lower_bound families hG hρ hε hεG hν hν_one hgap hgap_range,
    UpperModel.oracleComplexity_upper hG hρ hε hν hGε hgap⟩

end BoundaryLower
end WC
