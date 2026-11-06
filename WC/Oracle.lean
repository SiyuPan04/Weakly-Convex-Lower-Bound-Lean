import WC.Subgradient
import WC.Proximal
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The complete subdifferential oracle

The subdifferential is the actual Fréchet support set. Its nonemptiness is
proved by separating the strict epigraph of the convexified function.
Closedness, convexity, and compactness follow from its global support inequalities.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def subdifferential (f : E → ℝ) (x : E) : Set E := {v | FrechetSubgradient f x v}

theorem weakSubgradientSet_convex (ρ : ℝ) (f : E → ℝ) (x : E) :
    Convex ℝ {v | WeakSubgradient ρ f x v} := by
  intro v hv w hw a b ha hb hab y
  have hv' := mul_le_mul_of_nonneg_left (hv y) ha
  have hw' := mul_le_mul_of_nonneg_left (hw y) hb
  simp only [inner_add_left, real_inner_smul_left]
  have hb_eq : b = 1 - a := by linarith
  rw [hb_eq] at hw' ⊢
  nlinarith

theorem weakSubgradientSet_isClosed (ρ : ℝ) (f : E → ℝ) (x : E) :
    IsClosed {v | WeakSubgradient ρ f x v} := by
  have heq : {v | WeakSubgradient ρ f x v} =
      ⋂ y : E, {v | f x + inner ℝ v (y - x) - ρ / 2 * ‖y - x‖ ^ 2 ≤ f y} := by
    ext v
    simp [WeakSubgradient]
  rw [heq]
  apply isClosed_iInter
  intro y
  exact isClosed_le
    ((continuous_const.add (continuous_id.inner continuous_const)).sub continuous_const)
    continuous_const

theorem subdifferential_eq_weak {ρ : ℝ} {f : E → ℝ} (x : E)
    (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) :
    subdifferential f x = {v | WeakSubgradient ρ f x v} := by
  ext v
  exact (weakSubgradient_iff_frechet hρ hf).symm

theorem subdifferential_convex {ρ : ℝ} {f : E → ℝ} (x : E)
    (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) : Convex ℝ (subdifferential f x) := by
  rw [subdifferential_eq_weak x hρ hf]
  exact weakSubgradientSet_convex ρ f x

theorem subdifferential_isClosed {ρ : ℝ} {f : E → ℝ} (x : E)
    (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) : IsClosed (subdifferential f x) := by
  rw [subdifferential_eq_weak x hρ hf]
  exact weakSubgradientSet_isClosed ρ f x

theorem subdifferential_subset_closedBall {G : ℝ} {f : E → ℝ} (x : E)
    (hG : 0 ≤ G) (hf : GloballyLipschitz G f) :
    subdifferential f x ⊆ Metric.closedBall 0 G := by
  intro v hv
  simpa using (hv.norm_le hG hf)

theorem subdifferential_isCompact [ProperSpace E] {G ρ : ℝ} {f : E → ℝ} (x : E)
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : IsCompact (subdifferential f x) :=
  (isCompact_closedBall 0 G).of_isClosed_subset (subdifferential_isClosed x hρ hwc)
    (subdifferential_subset_closedBall x hG hlip)

/-- Hahn-Banach support at every point of a continuous, everywhere finite convex function. -/
theorem continuous_convex_has_subgradient [CompleteSpace E] {g : E → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hc : Continuous g) (x : E) :
    ∃ v, ConvexSubgradient g x v := by
  let S : Set (E × ℝ) := {p | g p.1 < p.2}
  have hSconv : Convex ℝ S := by simpa [S] using hg.convex_strict_epigraph
  have hSopen : IsOpen S := isOpen_lt (hc.comp continuous_fst) continuous_snd
  have hxS : (x, g x) ∉ S := by simp [S]
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hSconv hSopen hxS
  let a : StrongDual ℝ E := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := l (0, 1)
  have hsplit (y : E) (r : ℝ) : l (y, r) = a y + r * b := by
    have hpair : (y, r) = (y, (0 : ℝ)) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hpair, map_add, map_smul]
    rfl
  have hb : 0 < b := by
    have h := hl (x, g x + 1) (by change g x < g x + 1; linarith)
    rw [hsplit, hsplit] at h
    linarith
  have hboundary (y : E) : a x + g x * b ≤ a y + g y * b := by
    by_contra hfail
    have hgap : 0 < a x + g x * b - (a y + g y * b) := by linarith
    let δ := (a x + g x * b - (a y + g y * b)) / (2 * b)
    have hδ : 0 < δ := div_pos hgap (by positivity)
    have hδeq : δ * (2 * b) = a x + g x * b - (a y + g y * b) :=
      div_mul_cancel₀ _ (by positivity)
    have h := hl (y, g y + δ) (by change g y < g y + δ; linarith)
    rw [hsplit, hsplit] at h
    nlinarith
  refine ⟨(-b⁻¹) • (InnerProductSpace.toDual ℝ E).symm a, ?_⟩
  intro y
  simp only [real_inner_smul_left, InnerProductSpace.toDual_symm_apply, map_sub]
  have h := hboundary y
  have hid : b * (g x + -b⁻¹ * (a y - a x)) = b * g x + a x - a y := by
    field_simp
    ring
  have hmul : b * (g x + -b⁻¹ * (a y - a x)) ≤ b * g y := by
    rw [hid]
    linarith
  exact (mul_le_mul_iff_right₀ hb).mp hmul

/-- Nonemptiness of the actual weakly convex subdifferential. -/
theorem subdifferential_nonempty [CompleteSpace E] {G ρ : ℝ} {f : E → ℝ} (x : E)
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : (subdifferential f x).Nonempty := by
  have hc : Continuous (fun y : E => f y + ρ / 2 * ‖y‖ ^ 2) :=
    (hlip.continuous hG).add (continuous_const.mul (continuous_norm.pow 2))
  obtain ⟨w, hw⟩ := continuous_convex_has_subgradient hwc hc x
  refine ⟨w - ρ • x, ?_⟩
  apply (weakSubgradient_iff_frechet hρ hwc).1
  apply weakSubgradient_iff_convexification.mpr
  simpa using hw

/-- The paper's oracle codomain: actual nonempty compact convex subsets. -/
abbrev CompactConvexSets (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {S : TopologicalSpace.NonemptyCompacts E // Convex ℝ (S : Set E)}

instance nonemptyCompacts_measurableSpace (α : Type*) [TopologicalSpace α] :
    MeasurableSpace (TopologicalSpace.NonemptyCompacts α) := borel _

instance nonemptyCompacts_borelSpace (α : Type*) [TopologicalSpace α] :
    BorelSpace (TopologicalSpace.NonemptyCompacts α) := ⟨rfl⟩

instance compactConvexSets_measurableSpace (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : MeasurableSpace (CompactConvexSets E) := borel _

instance compactConvexSets_borelSpace (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : BorelSpace (CompactConvexSets E) := ⟨rfl⟩

def fullSubdifferential [ProperSpace E] [CompleteSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) : CompactConvexSets E :=
  ⟨{ carrier := subdifferential f x
     isCompact' := subdifferential_isCompact x hG hρ hlip hwc
     nonempty' := subdifferential_nonempty x hG hρ hlip hwc },
    subdifferential_convex x hρ hwc⟩

def fullOracle [ProperSpace E] [CompleteSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) : ℝ × CompactConvexSets E :=
  (f x, fullSubdifferential hG hρ hlip hwc x)

/-- The actual subdifferential has closed graph. -/
theorem subdifferential_graph_isClosed {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) :
    IsClosed {p : E × E | p.2 ∈ subdifferential f p.1} := by
  have heq : {p : E × E | p.2 ∈ subdifferential f p.1} =
      ⋂ y : E, {p : E × E | f p.1 + inner ℝ p.2 (y - p.1) -
        ρ / 2 * ‖y - p.1‖ ^ 2 ≤ f y} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, subdifferential_eq_weak p.1 hρ hwc,
      WeakSubgradient]
  rw [heq]
  apply isClosed_iInter
  intro y
  exact isClosed_le
    (((hlip.continuous hG).comp continuous_fst).add
      (continuous_snd.inner (continuous_const.sub continuous_fst)) |>.sub
      (continuous_const.mul ((continuous_const.sub continuous_fst).norm.pow 2))) continuous_const

/-- Meeting a fixed closed set is a closed condition, since all subgradients lie in one compact ball. -/
theorem subdifferential_hit_closed [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) {C : Set E} (hC : IsClosed C) :
    IsClosed {x : E | (subdifferential f x ∩ C).Nonempty} := by
  let K := Metric.closedBall (0 : E) G
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 G)
  let H : Set (E × K) := {p | (p.2 : E) ∈ subdifferential f p.1 ∧ (p.2 : E) ∈ C}
  have hH : IsClosed H := by
    have hc : Continuous (fun p : E × K => (p.1, (p.2 : E))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hgraph := (subdifferential_graph_isClosed hG hρ hlip hwc).preimage
      hc
    exact hgraph.inter (hC.preimage (continuous_subtype_val.comp continuous_snd))
  have hproj : IsClosed (Prod.fst '' H) := isClosedMap_fst_of_compactSpace H hH
  convert hproj using 1
  ext x
  constructor
  · rintro ⟨v, hv, hvC⟩
    exact ⟨(x, ⟨v, subdifferential_subset_closedBall x hG hlip hv⟩), ⟨hv, hvC⟩, rfl⟩
  · rintro ⟨⟨y, v⟩, hv, rfl⟩
    exact ⟨v, hv.1, hv.2⟩

theorem subdifferential_upperHemicontinuous [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : UpperHemicontinuous (subdifferential f) := by
  apply UpperHemicontinuous.of_forall_isOpen
  intro x U hU hxU
  have hclosed := subdifferential_hit_closed hG hρ hlip hwc hU.isClosed_compl
  have hEq : {x : E | (subdifferential f x ∩ Uᶜ).Nonempty}ᶜ =
      {x : E | subdifferential f x ⊆ U} := by
    ext x
    constructor
    · intro h v hv
      by_contra hvU
      exact h ⟨v, hv, hvU⟩
    · intro h hv
      obtain ⟨v, hv, hvU⟩ := hv
      exact hvU (h hv)
  have hopen := hclosed.isOpen_compl
  rw [hEq] at hopen
  exact hopen.mem_nhds hxU

theorem subdifferential_subset_isOpen [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) {U : Set E} (hU : IsOpen U) :
    IsOpen {x : E | subdifferential f x ⊆ U} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact (subdifferential_upperHemicontinuous hG hρ hlip hwc).forall_isOpen x U hU hx

/-- Open hit sets are Borel: exhaust the open target by countably many closed sets. -/
theorem subdifferential_hit_open_measurable [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) {U : Set E} (hU : IsOpen U) :
    MeasurableSet {x : E | (subdifferential f x ∩ U).Nonempty} := by
  obtain ⟨C, hC, hCU, hUnion, _⟩ := hU.exists_iUnion_isClosed
  have heq : {x : E | (subdifferential f x ∩ U).Nonempty} =
      ⋃ n : ℕ, {x : E | (subdifferential f x ∩ C n).Nonempty} := by
    ext x
    constructor
    · rintro ⟨v, hv, hvU⟩
      rw [← hUnion] at hvU
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hvU
      exact Set.mem_iUnion.mpr ⟨n, v, hv, hn⟩
    · intro hx
      obtain ⟨n, v, hv, hvC⟩ := Set.mem_iUnion.mp hx
      exact ⟨v, hv, hCU n hvC⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (subdifferential_hit_closed hG hρ hlip hwc (hC n)).measurableSet

/-- Borel measurability in the nonempty-compact Hausdorff topology. -/
theorem compactSubdifferential_measurable [ProperSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) :
    Measurable (fun x => (fullSubdifferential hG hρ hlip hwc x).val) := by
  change @Measurable E (TopologicalSpace.NonemptyCompacts E) _
    (borel (TopologicalSpace.NonemptyCompacts E)) _
  rw [TopologicalSpace.NonemptyCompacts.isTopologicalBasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨u, ⟨hufin, _, huopen⟩, rfl⟩
  change MeasurableSet {x : E | subdifferential f x ⊆ ⋃₀ u ∧
    ∀ U ∈ u, (subdifferential f x ∩ U).Nonempty}
  have hupper : MeasurableSet {x : E | subdifferential f x ⊆ ⋃₀ u} :=
    (subdifferential_subset_isOpen hG hρ hlip hwc (isOpen_sUnion huopen)).measurableSet
  have hhit : MeasurableSet (⋂ U ∈ u, {x : E | (subdifferential f x ∩ U).Nonempty}) :=
    hufin.measurableSet_biInter fun U hU =>
      subdifferential_hit_open_measurable hG hρ hlip hwc (huopen U hU)
  simpa only [Set.setOf_and, Set.setOf_forall] using hupper.inter hhit

theorem fullSubdifferential_measurable [ProperSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : Measurable (fullSubdifferential hG hρ hlip hwc) := by
  change @Measurable E (CompactConvexSets E) _ (borel (CompactConvexSets E)) _
  rw [borel_comap]
  exact (compactSubdifferential_measurable hG hρ hlip hwc).subtype_mk

/-- The complete oracle has the paper's Borel codomain, with no measurability assumption. -/
theorem fullOracle_measurable [ProperSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : Measurable (fullOracle hG hρ hlip hwc) :=
  (hlip.continuous hG).measurable.prodMk (fullSubdifferential_measurable hG hρ hlip hwc)

end WC
