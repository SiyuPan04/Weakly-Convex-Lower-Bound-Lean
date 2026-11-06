import MP.Concentration

/-! Adaptive exponential projection tails from actual stabilizer averaging.
The query's invariance under the hidden stabilizer is a deterministic
prefix-dependence identity, and no conditional-law assertion is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace MP.Concentration
open WC.Frame

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem column_projection_tail_real {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ E) {v : E} (hv : ‖v‖ = 1) (y : E)
    {B a : ℝ} (hB : 0 < B) (hy : ‖y‖ ≤ B) (ha : 0 < a) :
    (haar E).real {h | a ≤ |inner ℝ (act E h v) y|} ≤
      2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
  have hs : MeasurableSet {u : E | a ≤ |inner ℝ u y|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hh := sphere_projection_tail_real (columnLaw E v) (columnLaw_invariant E v)
    (columnLaw_unit_norm E hv) hd b y hB hy ha
  have heq : (columnLaw E v).real {u : E | a ≤ |inner ℝ u y|} =
      (haar E).real {h | a ≤ |inner ℝ (act E h v) y|} := by
    simp only [measureReal_def, columnLaw, Measure.map_apply (continuous_column E v).measurable hs]
    rfl
  rwa [heq] at hh

variable (W : Submodule ℝ E) [Nontrivial Wᗮ]

theorem adaptive_projection_tail_of_bound_real {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a) (query_bound : ∀ g, ‖query g‖ ≤ B) :
    (haar E).real {g | a ≤ |inner ℝ (act E g (v : E)) (query g)|} ≤
      2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
  let A : Orthogonal E → ℝ := fun g => if a ≤ |inner ℝ (act E g (v : E)) (query g)| then 1 else 0
  let F : Orthogonal E → Orthogonal Wᗮ → ℝ := fun g h =>
    if a ≤ |inner ℝ (act E g (act Wᗮ h v : E)) (query g)| then 1 else 0
  have hmeas : Measurable (Function.uncurry F) := by
    have hi : Measurable (fun p : Orthogonal E × Orthogonal Wᗮ =>
        |inner ℝ ((p.1 : E →L[ℝ] E) ((p.2 : Wᗮ →L[ℝ] Wᗮ) v : E)) (query p.1)|) := by fun_prop
    exact measurable_const.ite (measurableSet_le measurable_const hi) measurable_const
  have hbounded (g : Orthogonal E) (h : Orthogonal Wᗮ) : ‖F g h‖ ≤ 1 := by
    dsimp [F]
    split_ifs <;> norm_num
  have hint : Integrable (Function.uncurry F) ((haar E).prod (haar Wᗮ)) :=
    (integrable_const 1).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbounded p.1 p.2))
  have hshift (h : Orthogonal Wᗮ) : (∫ g, F g h ∂haar E) = ∫ g, A g ∂haar E := by
    have heq : (fun g => F g h) = (fun g => A (g * embed E W h)) := by
      funext g
      dsimp only [F, A]
      rw [query_fixed, act_mul, embed_apply_hidden]
    rw [heq, integral_mul_right_eq_self]
  have hpoint (g : Orthogonal E) : (∫ h, F g h ∂haar Wᗮ) ≤
      2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
    let y : Wᗮ := Wᗮ.orthogonalProjectionOnto ((act E g).symm (query g))
    have heq : (fun h => F g h) = (fun h : Orthogonal Wᗮ =>
        if a ≤ |inner ℝ (act Wᗮ h v) y| then (1 : ℝ) else 0) := by
      funext h
      dsimp only [F, y]
      rw [Wᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]
      have he := (act E g).inner_map_map (act Wᗮ h v : E) ((act E g).symm (query g))
      simp only [LinearIsometryEquiv.apply_symm_apply] at he
      rw [he]
    rw [heq]
    have hs : MeasurableSet {h : Orthogonal Wᗮ | a ≤ |inner ℝ (act Wᗮ h v) y|} := by
      change MeasurableSet {h : Orthogonal Wᗮ | a ≤ |inner ℝ ((h : Wᗮ →L[ℝ] Wᗮ) v) y|}
      exact measurableSet_le measurable_const (by fun_prop)
    have hnorm : ‖y‖ ≤ B :=
      (Wᗮ.norm_orthogonalProjectionOnto_apply_le _).trans
        (by simpa only [LinearIsometryEquiv.norm_map] using query_bound g)
    have htail := column_projection_tail_real Wᗮ hd b hv y hB hnorm ha
    have hmeasure := integral_indicator_one (μ := haar Wᗮ) hs
    change (∫ h, if a ≤ |inner ℝ (act Wᗮ h v) y| then (1 : ℝ) else 0 ∂haar Wᗮ) = _ at hmeasure
    rw [hmeasure]
    exact htail
  have havg : (∫ g, A g ∂haar E) ≤ 2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
    calc
      (∫ g, A g ∂haar E) = ∫ h, ∫ g, F g h ∂haar E ∂haar Wᗮ := by simp_rw [hshift]; simp
      _ = ∫ g, ∫ h, F g h ∂haar Wᗮ ∂haar E := (integral_integral_swap hint).symm
      _ ≤ ∫ _g, 2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) ∂haar E :=
        integral_mono_ae hint.integral_prod_left (integrable_const _) (Filter.Eventually.of_forall hpoint)
      _ = _ := by simp
  have hs : MeasurableSet {g : Orthogonal E | a ≤ |inner ℝ (act E g (v : E)) (query g)|} := by
    change MeasurableSet {g : Orthogonal E | a ≤ |inner ℝ ((g : E →L[ℝ] E) (v : E)) (query g)|}
    exact measurableSet_le measurable_const (by fun_prop)
  have heq := integral_indicator_one (μ := haar E) hs
  change (∫ g, A g ∂haar E) = _ at heq
  rwa [heq] at havg

theorem adaptive_projection_tail_real {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    (haar E).real {g | ‖query g‖ ≤ B ∧ a ≤ |inner ℝ (act E g (v : E)) (query g)|} ≤
      2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
  let q := confinedQuery E B query
  have hqmeas : Measurable q := measurable_confinedQuery E B query measurable_query
  have hqbound : ∀ g, ‖q g‖ ≤ B := confinedQuery_bound E hB.le query
  have hqfixed : ∀ g h, q (g * embed E W h) = q g := confinedQuery_fixed E W B query query_fixed
  have htail := adaptive_projection_tail_of_bound_real E W hd b v hv q hqmeas hqfixed hB ha hqbound
  have hsubset : {g : Orthogonal E | ‖query g‖ ≤ B ∧ a ≤ |inner ℝ (act E g (v : E)) (query g)|} ⊆
      {g | a ≤ |inner ℝ (act E g (v : E)) (q g)|} := by
    intro g hg
    change a ≤ |inner ℝ (act E g (v : E)) (q g)|
    rw [show q g = query g from if_pos hg.1]
    exact hg.2
  exact (measureReal_mono hsubset).trans htail

theorem adaptive_projection_tail {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E → E) (measurable_query : Measurable query)
    (query_fixed : ∀ g h, query (g * embed E W h) = query g)
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    haar E {g | ‖query g‖ ≤ B ∧ a ≤ |inner ℝ (act E g (v : E)) (query g)|} ≤
      ENNReal.ofReal (2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2))) := by
  have h := ENNReal.ofReal_le_ofReal
    (adaptive_projection_tail_real E W hd b v hv query measurable_query query_fixed hB ha)
  rwa [ofReal_measureReal] at h

/-- Joint exponential tail for an actual independent private seed.
The estimate is uniform over every adaptive prefix-measurable query. -/
theorem adaptive_projection_tail_product {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] {d : ℕ} (hd : 0 < d)
    (b : OrthonormalBasis (Fin d) ℝ Wᗮ) (v : Wᗮ) (hv : ‖v‖ = 1)
    (query : Orthogonal E × S → E) (measurable_query : Measurable query)
    (query_fixed : ∀ s g h, query (g * embed E W h, s) = query (g, s))
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    ((haar E).prod ν) {p | ‖query p‖ ≤ B ∧
        a ≤ |inner ℝ (act E p.1 (v : E)) (query p)|} ≤
      ENNReal.ofReal (2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2))) := by
  have hcolumn : Measurable (fun p : Orthogonal E × S => act E p.1 (v : E)) :=
    (continuous_column E (v : E)).measurable.comp measurable_fst
  have hinner : Measurable (fun p : Orthogonal E × S =>
      |inner ℝ (act E p.1 (v : E)) (query p)|) := by fun_prop
  have hset : MeasurableSet {p : Orthogonal E × S | ‖query p‖ ≤ B ∧
      a ≤ |inner ℝ (act E p.1 (v : E)) (query p)|} :=
    (measurableSet_le measurable_query.norm measurable_const).inter
      (measurableSet_le measurable_const hinner)
  rw [Measure.prod_apply_symm hset]
  calc
    (∫⁻ s, haar E ((fun g => (g, s)) ⁻¹' {p | ‖query p‖ ≤ B ∧
        a ≤ |inner ℝ (act E p.1 (v : E)) (query p)|}) ∂ν) ≤
        ∫⁻ _s, ENNReal.ofReal (2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2))) ∂ν := by
      apply lintegral_mono
      intro s
      change haar E {g | ‖query (g, s)‖ ≤ B ∧
        a ≤ |inner ℝ (act E g (v : E)) (query (g, s))|} ≤ _
      exact adaptive_projection_tail E W hd b v hv (fun g => query (g, s))
        (measurable_query.comp (measurable_id.prodMk measurable_const))
        (query_fixed s) hB ha
    _ = _ := by simp

end MP.Concentration
