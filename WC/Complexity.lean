import WC.ModelMeasurability
import Mathlib.Tactic.ENatToNat

/-! Definition-level lower and upper bounds for the exact trajectory complexity.
The hard-instance and algorithm constructions must be supplied separately. -/

noncomputable section
namespace WC.Model

open scoped ENNReal

theorem hittingTime_le_of_success {G ρ Δ ε ν : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (t : ℕ)
    (hsuccess : ENNReal.ofReal (1 - ν) ≤ successProbability hG hρ A I ε t) :
    hittingTime hG hρ A I ε ν ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le ⟨t, hsuccess⟩ le_rfl

theorem hittingTime_lower_bound {G ρ Δ ε ν : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (T : ℕ)
    (hfailure : ∀ t ≤ T, successProbability hG hρ A I ε t < ENNReal.ofReal (1 - ν)) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ hittingTime hG hρ A I ε ν := by
  apply le_iInf
  intro t
  have hT : T + 1 ≤ t.val := by
    by_contra h
    have ht : t.val ≤ T := by omega
    exact (not_lt_of_ge t.property) (hfailure t.val ht)
  exact_mod_cast hT

/-- Simultaneous failure through `T` on one instance per algorithm gives `T+1`. -/
theorem oracleComplexity_lower_bound {G ρ Δ ε ν : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (T : ℕ)
    (hhard : ∀ A : BorelAlgorithm, ∃ I : Instance G ρ Δ,
      ∀ t ≤ T, successProbability hG hρ A I ε t < ENNReal.ofReal (1 - ν)) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ oracleComplexity G ρ Δ ε ν hG hρ := by
  apply le_iInf
  intro A
  obtain ⟨I, hI⟩ := hhard A
  exact le_iSup_of_le I (hittingTime_lower_bound hG hρ A I T hI)

theorem oracleComplexity_upper_bound {G ρ Δ ε ν : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (C : ℝ≥0∞)
    (halgorithm : ∀ I : Instance G ρ Δ, ∃ t : ℕ,
      (t : ℝ≥0∞) ≤ C ∧
      ENNReal.ofReal (1 - ν) ≤ successProbability hG hρ A I ε t) :
    oracleComplexity G ρ Δ ε ν hG hρ ≤ C := by
  apply iInf_le_of_le A
  apply iSup_le
  intro I
  obtain ⟨t, ht, hs⟩ := halgorithm I
  exact (hittingTime_le_of_success hG hρ A I t hs).trans ht

end WC.Model
