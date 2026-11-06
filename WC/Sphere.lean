import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Rotational invariance and the spherical second moment

The second-moment theorem here is stated for an actual probability
measure invariant under every orthogonal linear isometry and supported
almost everywhere on the unit sphere. It proves the moment identity
from those measure-theoretic properties; it does not assume the identity.
Conditional laws of unexposed columns in a random frame are a separate
step of the manuscript's rotation argument.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WC
namespace Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Invariance of an actual measure under every orthogonal transformation. -/
def RotationallyInvariant (μ : Measure E) : Prop :=
  ∀ e : E ≃ₗᵢ[ℝ] E, Measure.map e μ = μ

omit [FiniteDimensional ℝ E] in
/-- The spherical inner-product moment is integrable, by Cauchy--Schwarz. -/
theorem inner_sq_integrable (μ : Measure E) [IsFiniteMeasure μ]
    (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1) (x : E) :
    Integrable (fun u => (inner ℝ u x) ^ 2) μ := by
  apply (integrable_const (‖x‖ ^ 2)).mono' (by fun_prop)
  filter_upwards [unit_norm] with u hu
  have hb := abs_real_inner_le_norm u x
  rw [hu, one_mul] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb

omit [FiniteDimensional ℝ E] in
/-- Orthogonal invariance makes equal-length directions have equal
second moments. Reflection in the perpendicular bisector supplies an
explicit orthogonal transformation between the directions. -/
theorem inner_sq_integral_eq_of_norm_eq (μ : Measure E)
    (invariant : RotationallyInvariant μ) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    (∫ u, (inner ℝ u x) ^ 2 ∂μ) = ∫ u, (inner ℝ u y) ^ 2 ∂μ := by
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, invariant e⟩
  have hi := hp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun u => (inner ℝ u y) ^ 2)
  have hfun : (fun u => (inner ℝ (e u) y) ^ 2) =
      (fun u => (inner ℝ u x) ^ 2) := by
    funext u
    rw [← he, e.inner_map_map]
  rw [hfun] at hi
  exact hi

omit [FiniteDimensional ℝ E] in
/-- The exact spherical second moment in positive dimension. -/
theorem inner_sq_integral (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E) :
    (∫ u, (inner ℝ u x) ^ 2 ∂μ) = ‖x‖ ^ 2 / d := by
  let i₀ : Fin d := ⟨0, hd⟩
  let c : ℝ := ∫ u, (inner ℝ u (b i₀)) ^ 2 ∂μ
  have coordinate_eq (i : Fin d) :
      (∫ u, (inner ℝ u (b i)) ^ 2 ∂μ) = c := by
    apply inner_sq_integral_eq_of_norm_eq μ invariant
    simp [b.orthonormal.norm_eq_one]
  have trace : (d : ℝ) * c = 1 := by
    calc
      (d : ℝ) * c = ∑ _i : Fin d, c := by simp
      _ = ∑ i : Fin d, ∫ u, (inner ℝ u (b i)) ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (coordinate_eq i).symm
      _ = ∫ u, ∑ i : Fin d, (inner ℝ u (b i)) ^ 2 ∂μ :=
        (integral_finsetSum _ (fun i _ => inner_sq_integrable μ unit_norm (b i))).symm
      _ = ∫ u, ‖u‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => b.sum_sq_inner_left u)
      _ = 1 := by
        have heq : (fun u => ‖u‖ ^ 2) =ᵐ[μ] (fun _ => (1 : ℝ)) :=
          unit_norm.mono (fun u hu => by simp [hu])
        rw [integral_congr_ae heq]
        simp
  have hrotate : (∫ u, (inner ℝ u x) ^ 2 ∂μ) =
      ∫ u, (inner ℝ u (‖x‖ • b i₀)) ^ 2 ∂μ := by
    apply inner_sq_integral_eq_of_norm_eq μ invariant
    simp [norm_smul, b.orthonormal.norm_eq_one]
  have hdim : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  rw [hrotate]
  simp only [real_inner_smul_right, mul_pow]
  rw [integral_const_mul]
  change ‖x‖ ^ 2 * c = ‖x‖ ^ 2 / (d : ℝ)
  apply (eq_div_iff hdim).mpr
  nlinarith [trace]

variable (E) in
/-- Normalized Lebesgue measure on the open unit ball. -/
def ballProbability : Measure E :=
  (volume (Metric.ball (0 : E) 1))⁻¹ • volume.restrict (Metric.ball (0 : E) 1)

instance ballProbability_isProbabilityMeasure : IsProbabilityMeasure (ballProbability E) where
  measure_univ := by
    have hpos : volume (Metric.ball (0 : E) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
    have hfinite : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
    simp only [ballProbability, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos hfinite

/-- Every orthogonal transformation preserves normalized ball measure. -/
theorem ballProbability_invariant : RotationallyInvariant (ballProbability E) := by
  intro e
  rw [ballProbability, Measure.map_smul]
  congr 1
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    Measure.restrict_apply (e.continuous.measurable hs), Measure.restrict_apply hs]
  have hball : e ⁻¹' Metric.ball (0 : E) 1 = Metric.ball (0 : E) 1 := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  calc
    volume ((e ⁻¹' s) ∩ Metric.ball (0 : E) 1) =
        volume (e ⁻¹' (s ∩ Metric.ball (0 : E) 1)) := by rw [Set.preimage_inter, hball]
    _ = volume (s ∩ Metric.ball (0 : E) 1) := by
      rw [← Measure.map_apply e.continuous.measurable (hs.inter measurableSet_ball),
        e.measurePreserving.map_eq]

/-- Radial normalization, defined as zero at the origin. -/
def normalize (x : E) : E := ‖x‖⁻¹ • x

theorem measurable_normalize : Measurable (normalize : E → E) := by
  unfold normalize
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalize_norm {x : E} (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  simp [normalize, norm_smul, hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalize_isometry (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    normalize (e x) = e (normalize x) := by
  simp [normalize, e.norm_map]

variable (E) in
/-- The uniform sphere distribution obtained by radial projection of
normalized Lebesgue measure on the unit ball. -/
def uniform : Measure E := (ballProbability E).map normalize

instance uniform_isProbabilityMeasure : IsProbabilityMeasure (uniform E) :=
  Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable

/-- The constructed sphere distribution is invariant under all orthogonal maps. -/
theorem uniform_invariant : RotationallyInvariant (uniform E) := by
  intro e
  unfold uniform
  rw [Measure.map_map e.continuous.measurable measurable_normalize]
  have hcomp : (e ∘ normalize) = normalize ∘ e := by
    funext x
    exact (normalize_isometry e x).symm
  rw [hcomp, ← Measure.map_map measurable_normalize e.continuous.measurable,
    ballProbability_invariant e]

/-- In nonzero dimension the constructed measure is supported on the
actual unit sphere. The exceptional normalization at zero is a null event. -/
theorem uniform_unit_norm [Nontrivial E] : ∀ᵐ u ∂uniform E, ‖u‖ = 1 := by
  unfold uniform
  apply (ae_map_iff measurable_normalize.aemeasurable
    (measurable_norm (measurableSet_singleton (1 : ℝ)))).mpr
  apply Measure.ae_smul_measure (μ := volume.restrict (Metric.ball (0 : E) 1))
  filter_upwards [Measure.ae_ne (volume.restrict (Metric.ball (0 : E) 1)) (0 : E)] with x hx
  exact normalize_norm hx

/-- The exact second moment for the concrete uniform sphere distribution. -/
theorem uniform_inner_sq_integral [Nontrivial E] {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ E) (x : E) :
    (∫ u, (inner ℝ u x) ^ 2 ∂uniform E) = ‖x‖ ^ 2 / d :=
  inner_sq_integral (uniform E) uniform_invariant uniform_unit_norm hd b x

/-- The projection tail estimate obtained from the exact spherical
second moment and Markov's inequality, in real probability notation. -/
theorem uniform_projection_tail_real [Nontrivial E] {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ E) (x : E) {a : ℝ} (ha : 0 < a) :
    (uniform E).real {u | a < |inner ℝ u x|} ≤ ‖x‖ ^ 2 / ((d : ℝ) * a ^ 2) := by
  have hmoment := uniform_inner_sq_integral hd b x
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun u : E => sq_nonneg (inner ℝ u x)))
    (inner_sq_integrable (uniform E) uniform_unit_norm x) (a ^ 2)
  rw [hmoment] at hmarkov
  have hsubset : {u : E | a < |inner ℝ u x|} ⊆
      {u | a ^ 2 ≤ (inner ℝ u x) ^ 2} := by
    intro u hu
    change a ^ 2 ≤ (inner ℝ u x) ^ 2
    have hs := (sq_le_sq₀ (le_of_lt ha) (abs_nonneg (inner ℝ u x))).mpr (le_of_lt hu)
    simpa only [sq_abs] using hs
  have hmeasure := measureReal_mono (μ := uniform E) hsubset
  have hcombined : a ^ 2 * (uniform E).real {u | a < |inner ℝ u x|} ≤
      ‖x‖ ^ 2 / (d : ℝ) :=
    (mul_le_mul_of_nonneg_left hmeasure (sq_nonneg a)).trans hmarkov
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ (mul_pos hdreal (sq_pos_of_pos ha))).mpr
  have hm := (le_div_iff₀ hdreal).mp hcombined
  nlinarith [hm]

/-- The same actual probability bound in extended nonnegative reals. -/
theorem uniform_projection_tail [Nontrivial E] {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ E) (x : E) {a : ℝ} (ha : 0 < a) :
    uniform E {u | a < |inner ℝ u x|} ≤
      ENNReal.ofReal (‖x‖ ^ 2 / ((d : ℝ) * a ^ 2)) := by
  have h := ENNReal.ofReal_le_ofReal (uniform_projection_tail_real hd b x ha)
  rwa [ofReal_measureReal] at h

end Sphere
end WC
