import WC.AuxiliaryFamily
import WC.GeneralLowerReduction

/-! The convex auxiliary family gives an actual dimension-free minimax lower
bound of order G²/ε², uniformly in the confidence parameter below one. -/

noncomputable section
open scoped ENNReal
namespace WC
namespace BoundaryLower

theorem auxiliary_lower_bound {G ρ Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hb : 256 ≤ G ^ 2 / ε ^ 2) (hgap : ε ^ 2 ≤ ρ * Δ) :
    ENNReal.ofReal ((G ^ 2 / ε ^ 2) / 160) ≤
      Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  let accuracy := ε / G
  have haccPos : 0 < accuracy := div_pos hε hG
  have hprod : 256 * ε ^ 2 ≤ G ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mp hb
  have hsmall : accuracy ≤ 1 / 16 := by
    apply (div_le_iff₀ hG).mpr
    nlinarith [sq_nonneg (G - 16 * ε)]
  let K := auxiliaryLength accuracy
  let T := auxiliaryHorizon accuracy
  let η := auxiliaryEta accuracy K
  let δ := (1 - ν) / 2
  let d := K + 2 + ⌈4 * (K : ℕ) * (T + 1 : ℝ) * (9 : ℝ) ^ 2 / (δ * η ^ 2)⌉₊
  have hd : K + 2 ≤ d := by dsimp only [d]; omega
  have hdpos : 0 < d := by omega
  letI : NeZero d := ⟨ne_of_gt hdpos⟩
  let H := auxiliaryFamily (d := d) haccPos hsmall (show K ≤ d by omega)
  have hphysical_gap : (G ^ 2 / ρ) * H.gap ≤ Δ := by
    change (G ^ 2 / ρ) * accuracy ^ 2 ≤ Δ
    have hid : (G ^ 2 / ρ) * accuracy ^ 2 = ε ^ 2 / ρ := by dsimp [accuracy]; field_simp
    rw [hid]
    exact (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hgap)
  have haccuracy : ε ≤ G * H.threshold := by
    change ε ≤ G * (ε / G)
    rw [mul_div_cancel₀ _ hG.ne']
  have hdim : K + 2 +
      ⌈4 * (K : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 / (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d := by
    rfl
  have hcomplex : ((T + 1 : ℕ) : ℝ≥0∞) ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le :=
    Model.oracleComplexity_lower_bound hG.le hρ.le T
      (fun A => GeneralLowerReduction.family_physical_hard_instance H hG hρ hν hν_one
        hphysical_gap haccuracy hdim A)
  have hbounds := auxiliaryLength_bounds haccPos hsmall
  have hlow : G ^ 2 / ε ^ 2 ≤ 10 * (K : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hbounds.2.1
      (show 0 ≤ G ^ 2 / ε ^ 2 by positivity)
    have hid : (G ^ 2 / ε ^ 2) * (10 * (K : ℝ) * accuracy ^ 2) = 10 * (K : ℝ) := by
      dsimp [accuracy]
      field_simp
    change (G ^ 2 / ε ^ 2) * 1 ≤ (G ^ 2 / ε ^ 2) * (10 * (K : ℝ) * accuracy ^ 2) at hmul
    rw [mul_one, hid] at hmul
    exact hmul
  have hKT : K ≤ 16 * T := H.horizon_bound
  have hKTR : (K : ℝ) ≤ 16 * (T : ℝ) := by exact_mod_cast hKT
  have hcount : (G ^ 2 / ε ^ 2) / 160 ≤ (T : ℝ) := by linarith
  calc
    ENNReal.ofReal ((G ^ 2 / ε ^ 2) / 160) ≤ ENNReal.ofReal (T : ℝ) := ENNReal.ofReal_le_ofReal hcount
    _ = (T : ℝ≥0∞) := ENNReal.ofReal_natCast T
    _ ≤ ((T + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ T
    _ ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := hcomplex

end BoundaryLower
end WC

