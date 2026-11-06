import WC.Rotation
import WC.Complexity
import WC.MoreauScaling
import WC.Numerics

/-!
# Physical oracle scaling and the large-parameter lower reduction

All subdifferential transformations below concern the actual Fréchet
support set returned by `fullOracle`. The normalized-family existence
premise used by the final reduction is exactly the construction-dependent
input of the manuscript, and is not asserted to have been discharged here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WC
namespace LowerReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact positive scalar/spatial chain rule for a genuine Fréchet subgradient. -/
theorem FrechetSubgradient.scale {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : E → ℝ} {x v : E} (h : WC.FrechetSubgradient f (b • x) v) :
    WC.FrechetSubgradient (scaleFunction a b f) x ((a * b) • v) := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := h (ε / (a * b)) (div_pos hε (mul_pos ha hb))
  refine ⟨δ / b, div_pos hδ hb, ?_⟩
  intro y hy
  have hdist : ‖b • y - b • x‖ < δ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    have hm := (lt_div_iff₀ hb).mp hy
    nlinarith
  have hsupport := mul_le_mul_of_nonneg_left (hs (b • y) hdist) ha.le
  simp only [← smul_sub, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hb] at hsupport
  have heps : a * (ε / (a * b)) * b = ε := by field_simp
  have hepsnorm : a * (ε / (a * b)) * (b * ‖y - x‖) = ε * ‖y - x‖ := by
    calc
      a * (ε / (a * b)) * (b * ‖y - x‖) = (a * (ε / (a * b)) * b) * ‖y - x‖ := by ring
      _ = ε * ‖y - x‖ := by rw [heps]
  dsimp only [scaleFunction]
  rw [real_inner_smul_left]
  nlinarith [hsupport, hepsnorm]

theorem scaled_subdifferential {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : E → ℝ) (x : E) :
    subdifferential (scaleFunction a b f) x =
      (fun v => (a * b) • v) '' subdifferential f (b • x) := by
  ext w
  constructor
  · intro hw
    have hpoint : b⁻¹ • (b • x) = x := inv_smul_smul₀ hb.ne' x
    have hbase : WC.FrechetSubgradient (scaleFunction a b f) (b⁻¹ • (b • x)) w := by
      rwa [hpoint]
    have hinverse := FrechetSubgradient.scale (inv_pos.mpr ha) (inv_pos.mpr hb) hbase
    have hfunction : scaleFunction a⁻¹ b⁻¹ (scaleFunction a b f) = f := by
      funext z
      simp [scaleFunction, smul_smul, ha.ne', hb.ne']
    rw [hfunction] at hinverse
    refine ⟨(a⁻¹ * b⁻¹) • w, hinverse, ?_⟩
    change (a * b) • ((a⁻¹ * b⁻¹) • w) = w
    rw [smul_smul]
    have hcoeff : (a * b) * (a⁻¹ * b⁻¹) = 1 := by field_simp
    rw [hcoeff, one_smul]
  · rintro ⟨v, hv, rfl⟩
    exact FrechetSubgradient.scale ha hb hv

/-- Scalar image in the actual compact-convex oracle codomain. -/
def scaleSubgradientSet (c : ℝ) (S : CompactConvexSets E) : CompactConvexSets E :=
  ⟨S.val.map (fun v => c • v) (continuous_const.smul continuous_id), by
    change Convex ℝ ((fun v : E => c • v) '' (S.val : Set E))
    exact S.property.linear_image (c • LinearMap.id)⟩

theorem scaleSubgradientSet_continuous (c : ℝ) : Continuous (scaleSubgradientSet (E := E) c) := by
  apply continuous_induced_rng.mpr
  exact ((continuous_const.smul continuous_id : Continuous (fun v : E => c • v)).nonemptyCompacts_map).comp
    continuous_subtype_val

def scaleReply (a c : ℝ) (r : ℝ × CompactConvexSets E) : ℝ × CompactConvexSets E :=
  (a * r.1, scaleSubgradientSet c r.2)

theorem scaleReply_continuous (a c : ℝ) : Continuous (scaleReply (E := E) a c) :=
  (continuous_const.mul continuous_fst).prodMk ((scaleSubgradientSet_continuous c).comp continuous_snd)

theorem physical_fullOracle [ProperSpace E] [CompleteSpace E]
    {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ) {f : E → ℝ}
    (hf : Admissible 1 1 Δ f) (x : E) :
    fullOracle hG.le hρ.le (physical_admissible_scale hG hρ hf).lipschitz
      (physical_admissible_scale hG hρ hf).weaklyConvex x =
    scaleReply (G ^ 2 / ρ) G
      (fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        hf.lipschitz hf.weaklyConvex ((ρ / G) • x)) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply TopologicalSpace.NonemptyCompacts.ext
    change subdifferential (scaleFunction (G ^ 2 / ρ) (ρ / G) f) x =
      (fun v => G • v) '' subdifferential f ((ρ / G) • x)
    rw [scaled_subdifferential (div_pos (sq_pos_of_pos hG) hρ) (div_pos hρ hG)]
    rw [(physical_scaling_constants hG.ne' hρ.ne').1]

theorem measurable_to_borel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (h : Measurable f) : @Measurable X Y (borel X) (borel Y) f :=
  h.mono (le_of_eq BorelSpace.measurable_eq) (le_of_eq BorelSpace.measurable_eq.symm)

/-- Simulate an algorithm for the physically scaled problem using the
normalized exact oracle, including its entire compact subdifferential. -/
def scaleAlgorithm (G ρ : ℝ) (A : Model.BorelAlgorithm) : Model.BorelAlgorithm where
  decision d t p := (ρ / G) • A.decision d t
    (p.1, fun j => scaleReply (G ^ 2 / ρ) G (p.2 j))
  measurable_decision d t := by
    apply measurable_to_borel
    have hreply : Measurable (fun p : ℝ × (Fin t → Model.Reply d) =>
        fun j => scaleReply (G ^ 2 / ρ) G (p.2 j)) := by
      apply measurable_pi_lambda
      intro j
      exact (scaleReply_continuous (E := Model.Space d) (G ^ 2 / ρ) G).measurable.comp
        ((measurable_pi_apply j).comp measurable_snd)
    exact ((A.measurable_decision_default d t).comp
      (measurable_fst.prodMk hreply)).const_smul (ρ / G)

abbrev physicalInstance {G ρ Δ Δ' : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (I : Model.Instance 1 1 Δ) (hgap : (G ^ 2 / ρ) * Δ ≤ Δ') : Model.Instance G ρ Δ' :=
  ⟨I.dimension, scaleFunction (G ^ 2 / ρ) (ρ / G) I.objective,
    ⟨(physical_admissible_scale hG hρ I.admissible).weaklyConvex,
      (physical_admissible_scale hG hρ I.admissible).lipschitz,
      (physical_admissible_scale hG hρ I.admissible).gap.mono hgap⟩⟩

/-- Exact trajectory transport, using the proved full-oracle scaling law. -/
theorem trajectory_transport {G ρ Δ Δ' : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (A : Model.BorelAlgorithm) (I : Model.Instance 1 1 Δ) (hgap : (G ^ 2 / ρ) * Δ ≤ Δ')
    (seed : ℝ) (t : ℕ) :
    Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (scaleAlgorithm G ρ A) I seed t =
      (ρ / G) • Model.trajectory hG.le hρ.le A (physicalInstance hG hρ I hgap) seed t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => rw [Model.trajectory, Model.trajectory]; simp
    | succ n =>
      rw [Model.trajectory, Model.trajectory]
      change (ρ / G) • A.decision I.dimension (n + 1) (_, _) = (ρ / G) • A.decision I.dimension (n + 1) (_, _)
      congr 1
      congr 1
      congr 1
      funext j
      dsimp only [Prod.fst, Prod.snd]
      rw [ih j.val j.isLt]
      exact (physical_fullOracle hG hρ I.admissible _).symm

/-- The decision at time `T` is an admissible arbitrary output rule. -/
def queryOutput (A : Model.BorelAlgorithm) (d T : ℕ) : Model.BorelOutputRule d T :=
  ⟨A.decision d T, A.measurable_decision d T⟩

theorem queryOutput_eq {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : Model.BorelAlgorithm) (I : Model.Instance G ρ Δ) (seed : ℝ)
    {T : ℕ} (hT : 0 < T) :
    Model.evaluatedOutput hG hρ A I (queryOutput A I.dimension T) seed =
      Model.trajectory hG hρ A I seed T := by
  cases T with
  | zero => omega
  | succ n => rw [Model.trajectory]; rfl

theorem probability_le_of_disjoint_barrier {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {success barrier : Set S}
    (measurable_success : MeasurableSet success) {δ : ℝ} (_hδ : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (large_barrier : ENNReal.ofReal (1 - δ) ≤ μ barrier)
    (disjoint : barrier ⊆ successᶜ) : μ success ≤ ENNReal.ofReal δ := by
  have hbound := large_barrier.trans (measure_mono disjoint)
  have hreal : 1 - δ ≤ μ.real successᶜ := by
    have h := ENNReal.toReal_mono (measure_ne_top μ successᶜ) hbound
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ_one), measureReal_def] using h
  have hsum : μ.real success + μ.real successᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) measurable_success
  have hs : μ.real success ≤ δ := by linarith
  have h := ENNReal.ofReal_le_ofReal hs
  rwa [ofReal_measureReal] at h

open Rotation.Normalized

theorem physical_barrier_transport {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hgap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ)
    (A : Model.BorelAlgorithm) {g : Orthogonal d} {seed : ℝ}
    (event : H.BarrierEvent (scaleAlgorithm G ρ A)
      (queryOutput (scaleAlgorithm G ρ A) d T) g seed) :
    ∀ t ≤ T, G * (1 / (32 * Real.sqrt N)) <
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.trajectory hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) seed t)‖ := by
  intro t ht
  have hb : 1 / (32 * Real.sqrt N) <
      ‖gradient (moreauEnvelope (1 / 2) (H.objective g))
        (Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
          (scaleAlgorithm G ρ A) (H.instanceOf g) seed t)‖ := by
    by_cases hlt : t < T
    · exact event.1 t hlt
    · have heq : t = T := by omega
      subst t
      have h := event.2
      erw [queryOutput_eq _ _ _ _ _ H.horizon_positive] at h
      exact h
  change G * (1 / (32 * Real.sqrt N)) <
    ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (scaleFunction (G ^ 2 / ρ) (ρ / G) (H.objective g))) _‖
  rw [physical_moreau_gradient_norm hG hρ (H.regularity g)]
  erw [← trajectory_transport hG hρ A (H.instanceOf g) hgap seed t]
  exact mul_lt_mul_of_pos_left hb hG

/-- One fixed physically scaled instance defeats the entire trajectory
through `T`, at every prescribed confidence level. -/
theorem family_physical_hard_instance {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) (hN : 256 ≤ N)
    {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hgap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ)
    (hε : ε ≤ G * (1 / (32 * Real.sqrt N)))
    (hdim : M * N + 2 +
      ⌈4 * (M * N : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 /
        (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d)
    (A : Model.BorelAlgorithm) :
    ∃ I : Model.Instance G ρ Δ, ∀ t ≤ T,
      Model.successProbability hG.le hρ.le A I ε t < ENNReal.ofReal (1 - ν) := by
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_one : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨g, hg⟩ := H.randomized_rotation hN (scaleAlgorithm G ρ A)
    (queryOutput (scaleAlgorithm G ρ A) d T) hδ hδ_one hdim
  let I := physicalInstance hG hρ (H.instanceOf g) hgap
  refine ⟨I, ?_⟩
  intro t ht
  have hsuccess : MeasurableSet {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (Model.trajectory hG.le hρ.le A I seed t)‖ ≤ ε} :=
    Model.stationarity_success_measurable hG.le hρ A I ε t
  have hdisjoint : {s | H.BarrierEvent (scaleAlgorithm G ρ A)
      (queryOutput (scaleAlgorithm G ρ A) d T) g s} ⊆
      {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
        (Model.trajectory hG.le hρ.le A I seed t)‖ ≤ ε}ᶜ := by
    intro seed hs
    have hb := physical_barrier_transport H hG hρ hgap A hs t ht
    intro hstationary
    exact (not_le_of_gt (hε.trans_lt hb)) hstationary
  have hprob := probability_le_of_disjoint_barrier Model.seedMeasure hsuccess hδ.le hδ_one.le hg hdisjoint
  have hstrict : ENNReal.ofReal δ < ENNReal.ofReal (1 - ν) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by dsimp [δ]; linarith)
  exact hprob.trans_lt hstrict

/-- The construction-dependent premise of Theorem `thm:scaling-reduction`.
The radius and tolerance are uniform in the ambient dimension, so a
sufficient finite dimension can be chosen after the confidence level. -/
def UniformFamilies : Prop :=
  ∀ M N : ℕ, 256 ≤ N → 2 ≤ M → M ≤ 2 ^ (8 * N) →
    ∃ T : ℕ, ∃ B η : ℝ, 0 < B ∧ 0 < η ∧
      ∀ (d : ℕ) (hd : NeZero d), M * N + 2 ≤ d →
        ∃ H : @Family d M N T hd, H.radius = B ∧ H.tolerance = η

theorem accuracy_below_barrier {G ε : ℝ} {N : ℕ}
    (hG : 0 < G) (hε : 0 < ε) (hN : 0 < N)
    (hNmax : (N : ℝ) ≤ (G ^ 2 / ε ^ 2) / 1024) :
    ε ≤ G * (1 / (32 * Real.sqrt N)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_right hNmax (sq_nonneg ε)
  have hcancel : (G ^ 2 / ε ^ 2 / 1024) * ε ^ 2 = G ^ 2 / 1024 := by field_simp
  rw [hcancel] at hmul
  have hsq : (32 * ε * Real.sqrt (N : ℝ)) ^ 2 ≤ G ^ 2 := by
    calc
      (32 * ε * Real.sqrt (N : ℝ)) ^ 2 = 1024 * ε ^ 2 * (N : ℝ) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hNreal.le]
        ring
      _ ≤ G ^ 2 := by nlinarith [hmul]
  have hprod : 32 * ε * Real.sqrt (N : ℝ) ≤ G := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 32 * Real.sqrt (N : ℝ))).mpr
  nlinarith [hprod]

/-- The full large-parameter scaling reduction with the paper's constant
`2^-29`. The only remaining premise is existence of normalized families
satisfying the paper's five stated construction conditions. -/
theorem scaling_reduction (families : UniformFamilies)
    {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hb : (2 : ℝ) ^ 18 ≤ G ^ 2 / ε ^ 2)
    (hs : (2 : ℝ) ^ 18 ≤ ρ * Δ / ε ^ 2)
    (hgap_range : Δ ≤ (G ^ 2 / ρ) * Real.exp ((G ^ 2 / ε ^ 2) / 200)) :
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  let b := G ^ 2 / ε ^ 2
  let r := ρ * Δ / G ^ 2
  let N := ⌊b / 1024⌋₊
  let M := ⌊r * (N : ℝ) / 3⌋₊
  have hr : 0 < r := div_pos (mul_pos hρ hΔ) (sq_pos_of_pos hG)
  have hbr : b * r = ρ * Δ / ε ^ 2 := by dsimp [b, r]; field_simp
  have hsbr : (2 : ℝ) ^ 18 ≤ b * r := by rw [hbr]; exact hs
  have hrange : r ≤ Real.exp (b / 200) := by
    apply (div_le_iff₀ (sq_pos_of_pos hG)).mpr
    calc
      ρ * Δ ≤ ρ * ((G ^ 2 / ρ) * Real.exp (b / 200)) :=
        mul_le_mul_of_nonneg_left hgap_range hρ.le
      _ = Real.exp (b / 200) * G ^ 2 := by field_simp
  have parameters : 256 ≤ N ∧ 2 ≤ M ∧ M ≤ 2 ^ (8 * N) ∧
      3 * (M : ℝ) / N ≤ r ∧
      b ^ 2 * r / (2 : ℝ) ^ 29 ≤ (((M - 1) * stagger N : ℕ) : ℝ) :=
    scaling_integer_parameters hb hr hsbr hrange
  obtain ⟨hN, hM, hMmax, hnormalized_gap, _⟩ := parameters
  obtain ⟨T, B, η, hB, hη, available⟩ := families M N hN hM hMmax
  let δ := (1 - ν) / 2
  let d := M * N + 2 +
    ⌈4 * (M * N : ℕ) * (T + 1 : ℝ) * B ^ 2 / (δ * η ^ 2)⌉₊
  have hd : M * N + 2 ≤ d := by dsimp only [d]; omega
  have hdpos : 0 < d := by omega
  letI : NeZero d := ⟨ne_of_gt hdpos⟩
  obtain ⟨H, hRadius, hTolerance⟩ := available d inferInstance hd
  have hphysical_gap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ := by
    calc
      (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ (G ^ 2 / ρ) * r :=
        mul_le_mul_of_nonneg_left hnormalized_gap (by positivity)
      _ = Δ := by dsimp [r]; field_simp
  have hNbounds := scaling_N_bounds hb
  have haccuracy : ε ≤ G * (1 / (32 * Real.sqrt N)) :=
    accuracy_below_barrier hG hε (by omega : 0 < N) hNbounds.2.2.1
  have hdim : M * N + 2 +
      ⌈4 * (M * N : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 /
        (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d := by
    rw [hRadius, hTolerance]
  have hcomplex : ((T + 1 : ℕ) : ℝ≥0∞) ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le :=
    Model.oracleComplexity_lower_bound hG.le hρ.le T
      (fun A => family_physical_hard_instance H hN hG hρ hν hν_one hphysical_gap haccuracy hdim A)
  have hrn : 12 ≤ r * (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hNbounds.2.1 hr.le
    norm_num at hsbr
    nlinarith
  have hMbounds := scaling_M_bounds hrn
  have hT : (M : ℝ) * (N : ℝ) / 16 ≤ T := by
    have hcast : ((M * N : ℕ) : ℝ) ≤ 16 * (T : ℝ) := by exact_mod_cast H.horizon_bound
    push_cast at hcast
    nlinarith
  have hcount : b ^ 2 * r / (2 : ℝ) ^ 29 ≤ (T : ℝ) :=
    scaling_horizon_constant (by dsimp [b]; positivity) hr.le hNbounds.2.1
      hMbounds.2.1 (Nat.cast_nonneg N) hT
  have hid : (1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4 = b ^ 2 * r / (2 : ℝ) ^ 29 := by
    dsimp [b, r]
    field_simp
  calc
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤ ENNReal.ofReal (T : ℝ) :=
      ENNReal.ofReal_le_ofReal (by rw [hid]; exact hcount)
    _ = (T : ℝ≥0∞) := ENNReal.ofReal_natCast T
    _ ≤ ((T + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ T
    _ ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := hcomplex

end LowerReduction
end WC
