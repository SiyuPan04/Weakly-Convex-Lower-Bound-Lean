import WC.CompactMaximumRule

/-! Joint Borel measurability of actual complete oracles in continuous parameter families. -/

noncomputable section
namespace WC

variable {D E : Type*} [TopologicalSpace D] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compactMap_hit_closed [ProperSpace E] (F : D → CompactConvexSets E) {G : ℝ}
    (hgraph : IsClosed {p : D × E | p.2 ∈ (F p.1).val})
    (hbound : ∀ x, ((F x).val : Set E) ⊆ Metric.closedBall 0 G)
    {C : Set E} (hC : IsClosed C) :
    IsClosed {x : D | (((F x).val : Set E) ∩ C).Nonempty} := by
  let K := Metric.closedBall (0 : E) G
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 G)
  let H : Set (D × K) := {p | (p.2 : E) ∈ (F p.1).val ∧ (p.2 : E) ∈ C}
  have hH : IsClosed H := by
    have hc : Continuous (fun p : D × K => (p.1, (p.2 : E))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (hgraph.preimage hc).inter (hC.preimage (continuous_subtype_val.comp continuous_snd))
  have hproj := isClosedMap_fst_of_compactSpace H hH
  convert hproj using 1
  ext x
  constructor
  · rintro ⟨v, hv, hvC⟩
    exact ⟨(x, ⟨v, hbound x hv⟩), ⟨hv, hvC⟩, rfl⟩
  · rintro ⟨⟨y, v⟩, hv, rfl⟩
    exact ⟨v, hv.1, hv.2⟩

theorem compactMap_subset_isOpen [ProperSpace E] (F : D → CompactConvexSets E) {G : ℝ}
    (hgraph : IsClosed {p : D × E | p.2 ∈ (F p.1).val})
    (hbound : ∀ x, ((F x).val : Set E) ⊆ Metric.closedBall 0 G)
    {U : Set E} (hU : IsOpen U) : IsOpen {x : D | ((F x).val : Set E) ⊆ U} := by
  have hclosed := compactMap_hit_closed F hgraph hbound hU.isClosed_compl
  have heq : {x : D | (((F x).val : Set E) ∩ Uᶜ).Nonempty}ᶜ =
      {x : D | ((F x).val : Set E) ⊆ U} := by
    ext x
    constructor
    · intro h v hv
      by_contra hvU
      exact h ⟨v, hv, hvU⟩
    · rintro h ⟨v, hv, hvU⟩
      exact hvU (h hv)
  have hopen := hclosed.isOpen_compl
  rwa [heq] at hopen

theorem compactMap_measurable_of_closedGraph_bound [ProperSpace E]
    [SecondCountableTopology E] [MeasurableSpace D] [BorelSpace D]
    (F : D → CompactConvexSets E) {G : ℝ}
    (hgraph : IsClosed {p : D × E | p.2 ∈ (F p.1).val})
    (hbound : ∀ x, ((F x).val : Set E) ⊆ Metric.closedBall 0 G) : Measurable F := by
  have hhit {U : Set E} (hU : IsOpen U) :
      MeasurableSet {x : D | (((F x).val : Set E) ∩ U).Nonempty} := by
    obtain ⟨C, hC, hCU, hUnion, _⟩ := hU.exists_iUnion_isClosed
    have heq : {x : D | (((F x).val : Set E) ∩ U).Nonempty} =
        ⋃ n : ℕ, {x : D | (((F x).val : Set E) ∩ C n).Nonempty} := by
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
    exact MeasurableSet.iUnion fun n => (compactMap_hit_closed F hgraph hbound (hC n)).measurableSet
  have hval : Measurable (fun x => (F x).val) := by
    change @Measurable D (TopologicalSpace.NonemptyCompacts E) _
      (borel (TopologicalSpace.NonemptyCompacts E)) _
    rw [TopologicalSpace.NonemptyCompacts.isTopologicalBasis.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro _ ⟨u, ⟨hufin, _, huopen⟩, rfl⟩
    change MeasurableSet {x : D | ((F x).val : Set E) ⊆ ⋃₀ u ∧
      ∀ U ∈ u, (((F x).val : Set E) ∩ U).Nonempty}
    have hu : MeasurableSet {x : D | ((F x).val : Set E) ⊆ ⋃₀ u} :=
      (compactMap_subset_isOpen F hgraph hbound (isOpen_sUnion huopen)).measurableSet
    have hv : MeasurableSet (⋂ U ∈ u, {x : D | (((F x).val : Set E) ∩ U).Nonempty}) :=
      hufin.measurableSet_biInter fun U hU => hhit (huopen U hU)
    simpa only [Set.setOf_and, Set.setOf_forall] using hu.inter hv
  change @Measurable D (CompactConvexSets E) _ (borel (CompactConvexSets E)) _
  rw [borel_comap]
  exact hval.subtype_mk

section Parameterized

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
variable [ProperSpace E] [CompleteSpace E] [SecondCountableTopology E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology α]

omit [SecondCountableTopology α] in
theorem parameterized_fullSubdifferential_measurable {G ρ : ℝ} {f : α → E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hlip : ∀ a, GloballyLipschitz G (f a)) (hwc : ∀ a, WeaklyConvex ρ (f a)) :
    Measurable (fun p : α × E => fullSubdifferential hG hρ (hlip p.1) (hwc p.1) p.2) := by
  apply compactMap_measurable_of_closedGraph_bound
  · have hgraph := parameterSubgradient_graph_isClosed hρ hc hwc
    have hcont : Continuous (fun p : (α × E) × E => (p.1.1, p.1.2, p.2)) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact hgraph.preimage hcont
  · intro p
    exact subdifferential_subset_closedBall p.2 hG (hlip p.1)

omit [SecondCountableTopology α] in
theorem parameterized_fullOracle_measurable {G ρ : ℝ} {f : α → E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hlip : ∀ a, GloballyLipschitz G (f a)) (hwc : ∀ a, WeaklyConvex ρ (f a)) :
    Measurable (fun p : α × E => fullOracle hG hρ (hlip p.1) (hwc p.1) p.2) :=
  hc.measurable.prodMk (parameterized_fullSubdifferential_measurable hG hρ hc hlip hwc)

end Parameterized
end WC
