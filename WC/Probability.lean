import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# General probability tools for the rotation argument

These results supply the finite union bound and the fixed-instance
averaging step in `thm:abstract-randomized` (manuscript lines 1163–1191).
They are genuine statements about measures, not an abstract predicate
asserting that a hard instance exists.

The space `U` below can eventually be the space of orthonormal frames,
and `S` the private seed space. No random-frame measure or conditional
spherical moment law is constructed in this file. In particular, the
per-test estimates required by the union bound remain explicit premises.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WC
namespace Probability

variable {Ω U S ι : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace S]

/-- The union of finitely many events has probability at most the
number of tests times a common bound. No independence is required. -/
theorem finite_union_bound (μ : Measure Ω) (I : Finset ι)
    (bad : ι → Set Ω) (p : ℝ≥0∞)
    (per_test : ∀ i ∈ I, μ (bad i) ≤ p) :
    μ (⋃ i ∈ I, bad i) ≤ (I.card : ℝ≥0∞) * p := by
  calc
    μ (⋃ i ∈ I, bad i) ≤ ∑ i ∈ I, μ (bad i) :=
      measure_biUnion_finset_le I bad
    _ ≤ ∑ _i ∈ I, p := Finset.sum_le_sum per_test
    _ = (I.card : ℝ≥0∞) * p := by simp [nsmul_eq_mul]

/-- The simultaneous good event is the complement of the union of
bad events. Its probability is at least one minus the test budget. -/
theorem simultaneous_good_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ι) (bad : ι → Set Ω) (p δ : ℝ≥0∞)
    (measurable_bad : ∀ i ∈ I, MeasurableSet (bad i))
    (per_test : ∀ i ∈ I, μ (bad i) ≤ p)
    (budget : (I.card : ℝ≥0∞) * p ≤ δ) :
    1 - δ ≤ μ (⋃ i ∈ I, bad i)ᶜ := by
  have hbad : μ (⋃ i ∈ I, bad i) ≤ δ :=
    (finite_union_bound μ I bad p per_test).trans budget
  rw [measure_compl (I.measurableSet_biUnion measurable_bad)
    (measure_ne_top μ _), measure_univ]
  exact tsub_le_tsub_left hbad 1

/-- Markov's inequality applied to a second moment. The random variable
is nonnegative and may be extended-real valued. The theorem does not
assert that any particular frame projection satisfies a moment bound. -/
theorem second_moment_tail (μ : Measure Ω) (f : Ω → ℝ≥0∞)
    (hf : Measurable f) (a : ℝ≥0∞) (ha : a ≠ 0) (ha_top : a ≠ ∞) :
    μ {ω | a ≤ f ω} ≤ (∫⁻ ω, (f ω) ^ 2 ∂μ) / a ^ 2 := by
  calc
    μ {ω | a ≤ f ω} ≤ μ {ω | a ^ 2 ≤ (f ω) ^ 2} :=
      measure_mono (fun _ h => ENNReal.pow_le_pow_left h)
    _ ≤ (∫⁻ ω, (f ω) ^ 2 ∂μ) / a ^ 2 :=
      meas_ge_le_lintegral_div (hf.pow_const 2).aemeasurable
        (pow_ne_zero 2 ha) (ENNReal.pow_ne_top ha_top)

/-- A measurable joint event under independent frame/seed sampling has
some fixed frame whose seed-section probability is at least the joint
probability. This handles a non-strict lower bound without assuming that
the section probabilities attain their supremum. -/
theorem exists_section_ge_joint (μ : Measure U) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (good : Set (U × S)) (measurable_good : MeasurableSet good) :
    ∃ u : U, (μ.prod ν) good ≤ ν (Prod.mk u ⁻¹' good) := by
  have finite_integral : (∫⁻ u, ν (Prod.mk u ⁻¹' good) ∂μ) ≠ ∞ := by
    rw [← Measure.prod_apply measurable_good]
    exact measure_ne_top (μ.prod ν) good
  obtain ⟨u, hu⟩ := exists_lintegral_le finite_integral
  exact ⟨u, (Measure.prod_apply measurable_good).trans_le hu⟩

/-- Fixed-instance extraction at any prescribed probability threshold.
The selected `u` is fixed before the private seed is drawn. -/
theorem exists_section_ge (μ : Measure U) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (good : Set (U × S)) (measurable_good : MeasurableSet good)
    (q : ℝ≥0∞) (joint_bound : q ≤ (μ.prod ν) good) :
    ∃ u : U, q ≤ ν (Prod.mk u ⁻¹' good) := by
  obtain ⟨u, hu⟩ := exists_section_ge_joint μ ν good measurable_good
  exact ⟨u, joint_bound.trans hu⟩

/-- Union bound followed by averaging over the frame. This is the
generic probability part of the randomized rotation proof; every
frame-specific per-test estimate must still be supplied. -/
theorem exists_fixed_parameter_good (μ : Measure U) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Finset ι) (bad : ι → Set (U × S)) (p δ : ℝ≥0∞)
    (measurable_bad : ∀ i ∈ I, MeasurableSet (bad i))
    (per_test : ∀ i ∈ I, (μ.prod ν) (bad i) ≤ p)
    (budget : (I.card : ℝ≥0∞) * p ≤ δ) :
    ∃ u : U, 1 - δ ≤ ν (Prod.mk u ⁻¹' (⋃ i ∈ I, bad i)ᶜ) := by
  apply exists_section_ge μ ν (⋃ i ∈ I, bad i)ᶜ
    (I.measurableSet_biUnion measurable_bad).compl (1 - δ)
  exact simultaneous_good_probability (μ.prod ν) I bad p δ
    measurable_bad per_test budget

end Probability
end WC
