import WC.Oracle
import WC.Moreau
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The exact oracle/algorithm/complexity model of Section 2. `MainTheorem` at the
end is the precise final proof target, a proposition rather than a proved
theorem. Defining this proposition does not discharge it.
-/

noncomputable section
namespace WC
namespace Model

open MeasureTheory
open scoped ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Reply (d : ℕ) := ℝ × CompactConvexSets (Space d)

/-- The private seed has the usual uniform distribution on `[0,1]`. -/
def seedMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance seedMeasure_probability : IsProbabilityMeasure seedMeasure where
  measure_univ := by simp [seedMeasure]

/-- A member of the dimension-free admissible function class. -/
structure Instance (G ρ Δ : ℝ) where
  dimension : ℕ
  objective : Space dimension → ℝ
  admissible : Admissible G ρ Δ objective

/-- Borel decision rules on every finite exact-oracle transcript. The query
at time zero is fixed separately to the origin, as in the manuscript. -/
structure BorelAlgorithm where
  decision (d t : ℕ) : ℝ × (Fin t → Reply d) → Space d
  measurable_decision (d t : ℕ) :
    @Measurable _ _ (borel _) (borel _) (decision d t)

def trajectory {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (seed : ℝ) (t : ℕ) : Space I.dimension :=
  match t with
  | 0 => 0
  | n + 1 => A.decision I.dimension (n + 1) (seed, fun s : Fin (n + 1) =>
      fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
        (trajectory hG hρ A I seed s.val))
termination_by t
decreasing_by exact s.isLt

@[simp] theorem trajectory_zero {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (seed : ℝ) :
    trajectory hG hρ A I seed 0 = 0 := by rw [trajectory]

def successProbability {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  seedMeasure {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
    (trajectory hG hρ A I seed t)‖ ≤ ε}

/-- Infimum over successful integer times; an empty indexing type gives `∞`. -/
def hittingTime {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (ε ν : ℝ) : ℝ≥0∞ :=
  ⨅ t : {t : ℕ // ENNReal.ofReal (1 - ν) ≤ successProbability hG hρ A I ε t},
    (t.val : ℝ≥0∞)

def oracleComplexity (G ρ Δ ε ν : ℝ) (hG : 0 ≤ G) (hρ : 0 ≤ ρ) : ℝ≥0∞ :=
  ⨅ A : BorelAlgorithm, ⨆ I : Instance G ρ Δ, hittingTime hG hρ A I ε ν

/-- A fixed-horizon arbitrary output need not be queried. -/
structure BorelOutputRule (d T : ℕ) where
  output : ℝ × (Fin T → Reply d) → Space d
  measurable_output : @Measurable _ _ (borel _) (borel _) output

/-- The complete target `thm:main`, not a declaration that it is proved. -/
def MainTheorem : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (G ρ Δ ε ν : ℝ) (hG : 0 < G) (hρ : 0 < ρ),
      0 ≤ ν → ν < 1 → 0 < ε → ε < min G (Real.sqrt (ρ * Δ)) →
      Δ ≤ G ^ 2 / ρ * Real.exp (G ^ 2 / (200 * ε ^ 2)) →
      ENNReal.ofReal (c * ρ * G ^ 2 * Δ / ε ^ 4) ≤
        oracleComplexity G ρ Δ ε ν hG.le hρ.le ∧
      oracleComplexity G ρ Δ ε ν hG.le hρ.le ≤
        ENNReal.ofReal (C * ρ * G ^ 2 * Δ / ε ^ 4)

end Model
end WC
