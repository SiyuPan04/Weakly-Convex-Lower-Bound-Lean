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

/-- Definition 1 with the manuscript's convention `ℕ = {1, 2, ...}`. -/
def positiveDimensionalInstances (G ρ Δ : ℝ) : Set (Instance G ρ Δ) :=
  {I | 0 < I.dimension}

/-- Definition 5 on all algorithms and exactly the positive-dimensional instances. -/
def positiveDimensionalComplexity (G ρ Δ ε ν : ℝ) (hG : 0 ≤ G) (hρ : 0 ≤ ρ) : ℝ≥0∞ :=
  oracleComplexityOn G ρ Δ ε ν hG hρ Set.univ (positiveDimensionalInstances G ρ Δ)

/-- In dimension zero the gradient is the unique vector, so time zero succeeds. -/
theorem hittingTime_zero_dimension {G ρ Δ ε ν : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (hd : I.dimension = 0)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) : WC.Model.hittingTime hG hρ A I ε ν = 0 := by
  have hzero : ∀ v : Space I.dimension, v = 0 := by
    rw [hd]
    exact fun v => Subsingleton.elim v 0
  have hs : WC.Model.successProbability hG hρ A I ε 0 = 1 := by
    unfold WC.Model.successProbability
    simp only [hzero (gradient _ _), norm_zero, hε, Set.setOf_true,
      MeasureTheory.measure_univ]
  have hhit : ENNReal.ofReal (1 - ν) ≤ WC.Model.successProbability hG hρ A I ε 0 := by
    rw [hs, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact le_antisymm (iInf_le_of_le ⟨0, hhit⟩ (by simp)) zero_le

/-- Adding dimension zero to the union in Definition 1 leaves the minimax
complexity unchanged: the extra instances have hitting time zero for every algorithm. -/
theorem positiveDimensionalComplexity_eq (G ρ Δ ε ν : ℝ) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) :
    positiveDimensionalComplexity G ρ Δ ε ν hG hρ = oracleComplexity G ρ Δ ε ν hG hρ := by
  unfold positiveDimensionalComplexity oracleComplexityOn oracleComplexity WC.Model.oracleComplexity
  apply le_antisymm
  · apply le_iInf
    intro A
    apply iInf_le_of_le ⟨A, Set.mem_univ _⟩
    apply iSup_le
    intro I
    exact le_iSup (fun J => WC.Model.hittingTime hG hρ A J ε ν) I.val
  · apply le_iInf
    intro A
    apply iInf_le_of_le A.val
    apply iSup_le
    intro I
    by_cases hd : 0 < I.dimension
    · exact le_iSup (fun J : {J : Instance G ρ Δ // J ∈ positiveDimensionalInstances G ρ Δ} =>
        WC.Model.hittingTime hG hρ A.val J.val ε ν) ⟨I, hd⟩
    · rw [hittingTime_zero_dimension hG hρ A.val I (by omega) hε hν]
      exact zero_le

/-- Theorem 2 of the manuscript, with the displayed constants and the full
oracle complexity from Definition 5. -/
def MainTheorem : Prop :=
  ∀ (G ρ Δ ε ν : ℝ) (hG : 0 < G) (hρ : 0 < ρ),
    0 < Δ → 0 < ε → ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ)) →
    Δ ≤ (G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2)) →
    0 ≤ ν → ν < 1 →
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      oracleComplexity G ρ Δ ε ν hG.le hρ.le

end Model
end WCLB
