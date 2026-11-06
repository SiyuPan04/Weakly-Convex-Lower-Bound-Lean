import WC.Sphere
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Haar distributed orthogonal frames

We construct the actual Haar probability on orthogonal operators. A
frame consists of the images of a fixed finite orthonormal family.
Adaptive projection estimates require a further stabilizer-averaging
argument; they are not built into the definition of the distribution.
-/

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open TopologicalSpace
open scoped ENNReal

namespace WC
namespace Frame

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- Orthogonal operators, represented inside the normed algebra of
continuous linear operators so that topology and Haar measure are concrete. -/
abbrev Orthogonal := unitary (E →L[ℝ] E)

instance orthogonal_measurableSpace : MeasurableSpace (Orthogonal E) := borel _
instance orthogonal_borelSpace : BorelSpace (Orthogonal E) := ⟨rfl⟩

instance orthogonal_compactSpace : CompactSpace (Orthogonal E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (CStarRing.norm_coe_unitary ⟨u, hu⟩)

/-- The full compact group, used as the normalization set for Haar measure. -/
def wholeGroup : PositiveCompacts (Orthogonal E) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar probability on the actual orthogonal group. -/
def haar : Measure (Orthogonal E) := Measure.haarMeasure (wholeGroup E)

instance haar_isProbabilityMeasure : IsProbabilityMeasure (haar E) where
  measure_univ := by
    exact Measure.haarMeasure_self

instance haar_isHaarMeasure : (haar E).IsHaarMeasure := by
  unfold haar
  infer_instance

/-- Compact orthogonal Haar probability is invariant on the right as well.
We derive this from uniqueness of probability Haar measures. -/
instance haar_isMulRightInvariant : IsMulRightInvariant (haar E) where
  map_mul_right_eq_self g := by
    let ν : Measure (Orthogonal E) := (haar E).map (fun h => h * g)
    haveI : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    haveI : IsMulLeftInvariant ν := by dsimp only [ν]; infer_instance
    haveI : ν.IsHaarMeasure :=
      isHaarMeasure_of_isCompact_nonempty_interior ν Set.univ isCompact_univ
        (by simp) (by simp) (by simp)
    exact isHaarMeasure_eq_of_isProbabilityMeasure ν (haar E)

/-- Orthogonal action on the ambient Euclidean space. -/
def act (g : Orthogonal E) : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv g

omit [Nontrivial E] in
theorem act_apply (g : Orthogonal E) (x : E) : act E g x = (g : E →L[ℝ] E) x := rfl

omit [Nontrivial E] in
theorem act_mul (g h : Orthogonal E) (x : E) :
    act E (g * h) x = act E g (act E h x) := rfl

omit [Nontrivial E] in
theorem continuous_column (x : E) : Continuous (fun g : Orthogonal E => act E g x) := by
  change Continuous (fun g : Orthogonal E => (g : E →L[ℝ] E) x)
  exact continuous_subtype_val.clm_apply continuous_const

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual distribution of one vector under a Haar orthogonal operator. -/
def columnLaw (x : E) : Measure E := (haar E).map (fun g => act E g x)

instance columnLaw_isProbabilityMeasure (x : E) : IsProbabilityMeasure (columnLaw E x) :=
  Measure.isProbabilityMeasure_map (continuous_column E x).measurable.aemeasurable

/-- Haar left invariance implies orthogonal invariance of each column law. -/
theorem columnLaw_invariant (x : E) : Sphere.RotationallyInvariant (columnLaw E x) := by
  intro e
  let k : Orthogonal E := Unitary.linearIsometryEquiv.symm e
  have hk : act E k = e := MulEquiv.apply_symm_apply _ _
  unfold columnLaw
  rw [Measure.map_map e.continuous.measurable (continuous_column E x).measurable]
  have heq : e ∘ (fun g => act E g x) = (fun g => act E g x) ∘ (fun g => k * g) := by
    funext g
    simp only [Function.comp_apply, act_mul, hk]
  rw [heq, ← Measure.map_map (continuous_column E x).measurable (measurable_const_mul k),
    map_mul_left_eq_self]

theorem columnLaw_unit_norm {x : E} (hx : ‖x‖ = 1) :
    ∀ᵐ u ∂columnLaw E x, ‖u‖ = 1 := by
  unfold columnLaw
  apply (ae_map_iff (continuous_column E x).measurable.aemeasurable
    (measurable_norm (measurableSet_singleton (1 : ℝ)))).mpr
  exact Filter.Eventually.of_forall (fun g => by simp [hx])

/-- A genuine Haar-distributed unit column has the spherical second moment. -/
theorem column_inner_sq_integral {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ E) {x : E} (hx : ‖x‖ = 1) (y : E) :
    (∫ g, (inner ℝ (act E g x) y) ^ 2 ∂haar E) = ‖y‖ ^ 2 / d := by
  have hmoment := Sphere.inner_sq_integral (columnLaw E x)
    (columnLaw_invariant E x) (columnLaw_unit_norm E hx) hd b y
  rw [columnLaw, integral_map (continuous_column E x).measurable.aemeasurable
    (by fun_prop)] at hmoment
  exact hmoment

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A finite family of columns of the Haar operator is an actual orthonormal frame. -/
theorem columns_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v)
    (g : Orthogonal E) : Orthonormal ℝ (fun i => act E g (v i)) :=
  (act E g).toLinearIsometry.orthonormal_comp_iff.mpr hv

section Stabilizer

variable (W : Submodule ℝ E)

/-- Extend an orthogonal transformation of the hidden subspace by the
identity on the exposed subspace. -/
def extendIsometry (h : Orthogonal Wᗮ) : E ≃ₗᵢ[ℝ] E :=
  W.orthogonalDecomposition.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ W)
      (act Wᗮ h)).trans W.orthogonalDecomposition.symm)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem extendIsometry_apply (h : Orthogonal Wᗮ) (x : E) :
    extendIsometry E W h x = (W.orthogonalProjectionOnto x : E) +
      (act Wᗮ h (Wᗮ.orthogonalProjectionOnto x) : E) := by
  simp [extendIsometry, LinearIsometryEquiv.trans_apply,
    Submodule.orthogonalDecomposition_symm_apply, LinearIsometryEquiv.withLpProdCongr]

/-- The same extension as an element of the concrete orthogonal group. -/
def embed (h : Orthogonal Wᗮ) : Orthogonal E :=
  Unitary.linearIsometryEquiv.symm (extendIsometry E W h)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem act_embed (h : Orthogonal Wᗮ) : act E (embed E W h) = extendIsometry E W h :=
  MulEquiv.apply_symm_apply _ _

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem embed_apply_hidden (h : Orthogonal Wᗮ) (x : Wᗮ) :
    act E (embed E W h) (x : E) = (act Wᗮ h x : E) := by
  rw [act_embed, extendIsometry_apply]
  simp [(W.starProjection_apply_eq_zero_iff).mpr x.property]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem embed_apply_exposed (h : Orthogonal Wᗮ) (x : W) :
    act E (embed E W h) (x : E) = x := by
  rw [act_embed, extendIsometry_apply]
  simp

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem coe_embed (h : Orthogonal Wᗮ) :
    (embed E W h : E →L[ℝ] E) =
      W.subtypeL.comp W.orthogonalProjectionOnto +
        Wᗮ.subtypeL.comp ((h : Wᗮ →L[ℝ] Wᗮ).comp Wᗮ.orthogonalProjectionOnto) := by
  ext x
  change act E (embed E W h) x = _
  rw [act_embed, extendIsometry_apply]
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_embed : Continuous (embed E W) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun h : Orthogonal Wᗮ => (embed E W h : E →L[ℝ] E))
  simp_rw [coe_embed]
  fun_prop

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A rule receiving only exposed columns is unchanged by hidden rotations. -/
theorem exposed_query_fixed {ι : Type*} (exposed : ι → W)
    (rule : (ι → E) → E) (g : Orthogonal E) (h : Orthogonal Wᗮ) :
    rule (fun i => act E (g * embed E W h) (exposed i : E)) =
      rule (fun i => act E g (exposed i : E)) := by
  congr 1
  funext i
  rw [act_mul, embed_apply_exposed]

variable [Nontrivial Wᗮ]

/-- A bounded query depending only on exposed directions has a small
second moment against a hidden Haar column. Instead of conditional
expectation, the proof averages right multiplication by the stabilizer
of the exposed space and applies Fubini. `query_fixed` is the precise
deterministic dependence condition, not an assumed probabilistic law. -/
theorem adaptive_inner_sq_le {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B : ℝ} (hB : 0 ≤ B) (query_bound : ∀ g, ‖query g‖ ≤ B) :
    (∫ g, (inner ℝ (act E g (v : E)) (query g)) ^ 2 ∂haar E) ≤
      B ^ 2 / (d : ℝ) := by
  let A : Orthogonal E → ℝ := fun g => (inner ℝ (act E g (v : E)) (query g)) ^ 2
  let F : Orthogonal E → Orthogonal Wᗮ → ℝ := fun g h =>
    (inner ℝ (act E g (act Wᗮ h v : E)) (query g)) ^ 2
  have hmeas : Measurable (Function.uncurry F) := by
    change Measurable (fun p : Orthogonal E × Orthogonal Wᗮ =>
      (inner ℝ ((p.1 : E →L[ℝ] E) ((p.2 : Wᗮ →L[ℝ] Wᗮ) v : E)) (query p.1)) ^ 2)
    fun_prop
  have hbounded (g : Orthogonal E) (h : Orthogonal Wᗮ) : ‖F g h‖ ≤ B ^ 2 := by
    have hunit : ‖act E g (act Wᗮ h v : E)‖ = 1 := by
      rw [(act E g).norm_map]
      change ‖act Wᗮ h v‖ = 1
      rw [(act Wᗮ h).norm_map, hv]
    have hinner := abs_real_inner_le_norm (act E g (act Wᗮ h v : E)) (query g)
    rw [hunit, one_mul] at hinner
    have hs := (sq_le_sq₀ (abs_nonneg _) hB).mpr (hinner.trans (query_bound g))
    change |(inner ℝ (act E g (act Wᗮ h v : E)) (query g)) ^ 2| ≤ B ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using hs
  have hint : Integrable (Function.uncurry F) ((haar E).prod (haar Wᗮ)) :=
    (integrable_const (B ^ 2)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbounded p.1 p.2))
  have hshift (h : Orthogonal Wᗮ) :
      (∫ g, F g h ∂haar E) = ∫ g, A g ∂haar E := by
    have heq : (fun g => F g h) = (fun g => A (g * embed E W h)) := by
      funext g
      dsimp only [F, A]
      rw [query_fixed, act_mul, embed_apply_hidden]
    rw [heq, integral_mul_right_eq_self]
  have hpoint (g : Orthogonal E) : (∫ h, F g h ∂haar Wᗮ) ≤ B ^ 2 / (d : ℝ) := by
    let y : Wᗮ := Wᗮ.orthogonalProjectionOnto ((act E g).symm (query g))
    have heq : (fun h => F g h) =
        (fun h => (inner ℝ (act Wᗮ h v) y) ^ 2) := by
      funext h
      dsimp only [F, y]
      rw [Wᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]
      have he := (act E g).inner_map_map (act Wᗮ h v : E) ((act E g).symm (query g))
      simp only [LinearIsometryEquiv.apply_symm_apply] at he
      rw [he]
    rw [heq, column_inner_sq_integral Wᗮ hd b hv]
    have hnorm : ‖y‖ ≤ B :=
      (Wᗮ.norm_orthogonalProjectionOnto_apply_le _).trans
        (by simpa only [LinearIsometryEquiv.norm_map] using query_bound g)
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ d)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hnorm
  calc
    (∫ g, A g ∂haar E) = ∫ h, ∫ g, F g h ∂haar E ∂haar Wᗮ := by
      simp_rw [hshift]
      simp
    _ = ∫ g, ∫ h, F g h ∂haar Wᗮ ∂haar E := (integral_integral_swap hint).symm
    _ ≤ ∫ _g, B ^ 2 / (d : ℝ) ∂haar E :=
      integral_mono_ae hint.integral_prod_left (integrable_const _)
        (Filter.Eventually.of_forall hpoint)
    _ = B ^ 2 / (d : ℝ) := by simp

/-- Clip a query to zero outside the confinement ball. This is solely a
device for estimating the joint event `‖query‖ ≤ B` and large projection. -/
def confinedQuery (B : ℝ) (query : Orthogonal E → E) (g : Orthogonal E) : E :=
  if ‖query g‖ ≤ B then query g else 0

omit [Nontrivial E] in
theorem measurable_confinedQuery (B : ℝ) (query : Orthogonal E → E)
    (hq : Measurable query) : Measurable (confinedQuery E B query) := by
  unfold confinedQuery
  exact hq.ite (measurableSet_le hq.norm measurable_const) measurable_const

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem confinedQuery_bound {B : ℝ} (hB : 0 ≤ B)
    (query : Orthogonal E → E) (g : Orthogonal E) : ‖confinedQuery E B query g‖ ≤ B := by
  unfold confinedQuery
  split_ifs with h
  · exact h
  · simpa using hB

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [Nontrivial Wᗮ] in
theorem confinedQuery_fixed (B : ℝ) (query : Orthogonal E → E)
    (hq : ∀ g h, query (g * embed E W h) = query g) (g : Orthogonal E) (h : Orthogonal Wᗮ) :
    confinedQuery E B query (g * embed E W h) = confinedQuery E B query g := by
  simp only [confinedQuery, hq g h]

/-- Actual small-projection probability for an arbitrary unbounded
query depending only on exposed directions. -/
theorem adaptive_projection_tail_real {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B a : ℝ} (hB : 0 ≤ B) (ha : 0 < a) :
    (haar E).real {g | ‖query g‖ ≤ B ∧ a < |inner ℝ (act E g (v : E)) (query g)|} ≤
      B ^ 2 / ((d : ℝ) * a ^ 2) := by
  let q := confinedQuery E B query
  have hqmeas : Measurable q := measurable_confinedQuery E B query measurable_query
  have hqbound : ∀ g, ‖q g‖ ≤ B := confinedQuery_bound E hB query
  have hqfixed : ∀ g h, q (g * embed E W h) = q g := confinedQuery_fixed E W B query query_fixed
  have hmoment := adaptive_inner_sq_le E W hd b v hv q hqmeas hqfixed hB hqbound
  have hint : Integrable (fun g => (inner ℝ (act E g (v : E)) (q g)) ^ 2) (haar E) := by
    apply (integrable_const (B ^ 2)).mono' (by
      change AEStronglyMeasurable
        (fun g : Orthogonal E => (inner ℝ ((g : E →L[ℝ] E) (v : E)) (q g)) ^ 2) (haar E)
      fun_prop)
    apply Filter.Eventually.of_forall
    intro g
    have hu : ‖act E g (v : E)‖ = 1 := by
      rw [(act E g).norm_map]
      exact hv
    have hb := abs_real_inner_le_norm (act E g (v : E)) (q g)
    rw [hu, one_mul] at hb
    have hs := (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb.trans (hqbound g))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using hs
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun g => sq_nonneg (inner ℝ (act E g (v : E)) (q g))))
    hint (a ^ 2)
  have hsubset : {g : Orthogonal E | ‖query g‖ ≤ B ∧
      a < |inner ℝ (act E g (v : E)) (query g)|} ⊆
      {g | a ^ 2 ≤ (inner ℝ (act E g (v : E)) (q g)) ^ 2} := by
    intro g hg
    change a ^ 2 ≤ (inner ℝ (act E g (v : E)) (q g)) ^ 2
    have hq : q g = query g := if_pos hg.1
    rw [hq]
    have hs := (sq_le_sq₀ (le_of_lt ha) (abs_nonneg _)).mpr (le_of_lt hg.2)
    simpa only [sq_abs] using hs
  have hmeasure := measureReal_mono (μ := haar E) hsubset
  have hcombined := (mul_le_mul_of_nonneg_left hmeasure (sq_nonneg a)).trans (hm.trans hmoment)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ (mul_pos hdreal (sq_pos_of_pos ha))).mpr
  have hmul := (le_div_iff₀ hdreal).mp hcombined
  nlinarith [hmul]

/-- Extended-real version, suitable for the finite union bound. -/
theorem adaptive_projection_tail {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B a : ℝ} (hB : 0 ≤ B) (ha : 0 < a) :
    haar E {g | ‖query g‖ ≤ B ∧ a < |inner ℝ (act E g (v : E)) (query g)|} ≤
      ENNReal.ofReal (B ^ 2 / ((d : ℝ) * a ^ 2)) := by
  have h := ENNReal.ofReal_le_ofReal
    (adaptive_projection_tail_real E W hd b v hv query measurable_query query_fixed hB ha)
  rwa [ofReal_measureReal] at h

/-- The same projection estimate with an independent private seed.
This is the joint probability needed before the fixed-frame averaging
step. Each seed-section is estimated by the proved Haar theorem. -/
theorem adaptive_projection_tail_product {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E × S → E) (measurable_query : Measurable query)
    (query_fixed : ∀ s g h, query (g * embed E W h, s) = query (g, s))
    {B a : ℝ} (hB : 0 ≤ B) (ha : 0 < a) :
    ((haar E).prod ν) {p | ‖query p‖ ≤ B ∧
        a < |inner ℝ (act E p.1 (v : E)) (query p)|} ≤
      ENNReal.ofReal (B ^ 2 / ((d : ℝ) * a ^ 2)) := by
  have hcolumn : Measurable (fun p : Orthogonal E × S => act E p.1 (v : E)) :=
    (continuous_column E (v : E)).measurable.comp measurable_fst
  have hinner : Measurable (fun p : Orthogonal E × S =>
      |inner ℝ (act E p.1 (v : E)) (query p)|) := by fun_prop
  have hset : MeasurableSet {p : Orthogonal E × S | ‖query p‖ ≤ B ∧
      a < |inner ℝ (act E p.1 (v : E)) (query p)|} :=
    (measurableSet_le measurable_query.norm measurable_const).inter
      (measurableSet_lt measurable_const hinner)
  rw [Measure.prod_apply_symm hset]
  calc
    (∫⁻ s, haar E ((fun g => (g, s)) ⁻¹' {p | ‖query p‖ ≤ B ∧
        a < |inner ℝ (act E p.1 (v : E)) (query p)|}) ∂ν) ≤
        ∫⁻ _s, ENNReal.ofReal (B ^ 2 / ((d : ℝ) * a ^ 2)) ∂ν := by
      apply lintegral_mono
      intro s
      change haar E {g | ‖query (g, s)‖ ≤ B ∧
        a < |inner ℝ (act E g (v : E)) (query (g, s))|} ≤ _
      exact adaptive_projection_tail E W hd b v hv (fun g => query (g, s))
        (measurable_query.comp (measurable_id.prodMk measurable_const))
        (query_fixed s) hB ha
    _ = ENNReal.ofReal (B ^ 2 / ((d : ℝ) * a ^ 2)) := by simp

end Stabilizer

end Frame
end WC
