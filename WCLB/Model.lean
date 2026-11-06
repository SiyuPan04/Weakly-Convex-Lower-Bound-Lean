import WC.Model

/-! The model and exact small-accuracy theorem of the WCLB manuscript.
The complete Hausdorff-Borel oracle and actual Moreau gradient are those
already proved in `WC`; no new oracle or stationarity surrogate is used. -/

noncomputable section
open scoped ENNReal
namespace WCLB
namespace Model

abbrev Space := WC.Model.Space
abbrev Reply := WC.Model.Reply
abbrev Instance := WC.Model.Instance
abbrev BorelAlgorithm := WC.Model.BorelAlgorithm
abbrev BorelOutputRule := WC.Model.BorelOutputRule
abbrev trajectory := @WC.Model.trajectory
abbrev successProbability := @WC.Model.successProbability
abbrev hittingTime := @WC.Model.hittingTime
abbrev oracleComplexity := WC.Model.oracleComplexity

/-- The manuscript's definition for arbitrary subclasses. Empty classes
are also defined; the manuscript uses this only for nonempty classes. -/
def oracleComplexityOn (G ρ Δ ε ν : ℝ) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (algorithms : Set BorelAlgorithm) (instances : Set (Instance G ρ Δ)) : ℝ≥0∞ :=
  ⨅ A : {A // A ∈ algorithms}, ⨆ I : {I // I ∈ instances},
    WC.Model.hittingTime hG hρ A.val I.val ε ν

/-- The exact conclusion of `thm:main`, including the existential universal
accuracy constant and a lower-bound constant independent of confidence. -/
def MainTheorem : Prop :=
  ∃ c₀ c : ℝ, 0 < c₀ ∧ 0 < c ∧
    ∀ (G ρ Δ ε ν : ℝ) (hG : 0 < G) (hρ : 0 < ρ),
      0 < Δ → 0 < ε → ε ≤ c₀ * min G (Real.sqrt (ρ * Δ)) →
      Δ ≤ (G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2)) →
      0 ≤ ν → ν < 1 →
      ENNReal.ofReal (c * ρ * G ^ 2 * Δ / ε ^ 4) ≤
        oracleComplexity G ρ Δ ε ν hG.le hρ.le

end Model
end WCLB
