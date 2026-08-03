import WeaklyConvexLowerBound.FullOracleModel
import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.Rotation
import WeaklyConvexLowerBound.Foundation.HiddenDirections

/-!
# Batch resisting directions for a full set-valued oracle

The one-direction construction in `FullSetResisting` is adequate for a
single-vector oracle, but a full subdifferential reply can expose several
base coordinates at the same round.  This file isolates the batch extension
needed by the manuscript.  If `I` is the set of base coordinates already
published and `N \subseteq Iᶜ` is the whole newly exposed set, all `|N|`
directions are installed simultaneously.

The important dimension count is

`|I| + |N| + (t+1) \le d + T`.

Thus the ambient dimension is `d+T`, rather than a bound of the form `2*T`.
The support definitions below inspect the entire set in an oracle reply; no
representative subgradient is selected.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The finite reply history before table entry `t`.  It is repeated here so
this batch module is independent of the older one-direction construction. -/
def batchTablePrefix {D K : Nat} (reply : Fin K → FullOracleReply D)
    (t : Fin K) : FullReplyHistory D t.1 :=
  fun i => reply ⟨i.1, by omega⟩

/-- A typed causal table: query `t` depends on exactly the first `t` complete
set-valued replies. -/
def BatchIsCausalTable {D K : Nat}
    (A : DeterministicFullOracleComponent D)
    (query : Fin K → EVector D) (reply : Fin K → FullOracleReply D) : Prop :=
  ∀ t, query t = A.nextQuery t.1 (batchTablePrefix reply t)

/-! ## The support of an entire set-valued reply -/

/-- Coordinates which occur in at least one vector of a set.  This is the
union of the supports of *all* vectors in `S`, not the support of a selected
representative. -/
def fullSetCoordinateSupport {D : Nat} (S : Set (EVector D)) : Finset (Fin D) :=
  by
    classical
    exact Finset.univ.filter fun i => ∃ g ∈ S, g i ≠ 0

/-- The coordinate support carried by the full subdifferential field of a
reply. -/
def fullReplyCoordinateSupport {D : Nat} (r : FullOracleReply D) :
    Finset (Fin D) :=
  fullSetCoordinateSupport r.subdiff

@[simp] theorem mem_fullSetCoordinateSupport_iff {D : Nat}
    {S : Set (EVector D)} {i : Fin D} :
    i ∈ fullSetCoordinateSupport S ↔ ∃ g ∈ S, g i ≠ 0 := by
  simp [fullSetCoordinateSupport]

@[simp] theorem mem_fullReplyCoordinateSupport_iff {D : Nat}
    {r : FullOracleReply D} {i : Fin D} :
    i ∈ fullReplyCoordinateSupport r ↔ ∃ g ∈ r.subdiff, g i ≠ 0 := by
  simp [fullReplyCoordinateSupport]

/-- Support with respect to a labelled family of ambient directions.  This
variant is useful after rotation: coordinate `i` is exposed precisely when
some member of the *whole* returned set has nonzero projection onto the
labelled direction `coordinate i`. -/
def fullSetSupportAlong {d D : Nat} (coordinate : Fin d → EVector D)
    (S : Set (EVector D)) : Finset (Fin d) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      ∃ g ∈ S, WeaklyConvexLowerBound.Foundation.evecDotValue (coordinate i) g ≠ 0

def fullReplySupportAlong {d D : Nat} (coordinate : Fin d → EVector D)
    (r : FullOracleReply D) : Finset (Fin d) :=
  fullSetSupportAlong coordinate r.subdiff

@[simp] theorem mem_fullReplySupportAlong_iff {d D : Nat}
    {coordinate : Fin d → EVector D} {r : FullOracleReply D} {i : Fin d} :
    i ∈ fullReplySupportAlong coordinate r ↔
      ∃ g ∈ r.subdiff,
        WeaklyConvexLowerBound.Foundation.evecDotValue (coordinate i) g ≠ 0 := by
  simp [fullReplySupportAlong, fullSetSupportAlong]

/-- All coordinates exposed by the full reply which have not previously
been published. -/
def newlyRevealedAlong {d D : Nat} (coordinate : Fin d → EVector D)
    (I : Finset (Fin d)) (r : FullOracleReply D) : Finset (Fin d) :=
  fullReplySupportAlong coordinate r \ I

theorem newlyRevealedAlong_subset_compl {d D : Nat}
    (coordinate : Fin d → EVector D) (I : Finset (Fin d))
    (r : FullOracleReply D) :
    newlyRevealedAlong coordinate I r ⊆ Iᶜ := by
  intro i hi
  simp only [newlyRevealedAlong, Finset.mem_sdiff] at hi
  simpa using hi.2

/-! ## The exact `d+T` dimension budget -/

/-- Already published and newly revealed base indices together use at most
the `d` base-coordinate slots. -/
theorem published_add_new_card_le_base {d : Nat}
    {I N : Finset (Fin d)} (hnew : N ⊆ Iᶜ) :
    I.card + N.card ≤ d := by
  have hdisj : Disjoint I N := by
    exact Finset.disjoint_left.2 fun i hiI hiN =>
      (Finset.mem_compl.1 (hnew hiN)) hiI
  have hunion : (I ∪ N).card ≤ (Finset.univ : Finset (Fin d)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  simpa using hunion

/-- At round `t<T`, the old base columns, every newly exposed base column,
and all queries `x⁰,…,xᵗ` fit in `ℝ^(d+T)`. -/
theorem batch_dimension_budget {d T t : Nat}
    {I N : Finset (Fin d)} (hnew : N ⊆ Iᶜ) (ht : t < T) :
    I.card + (t + 1) + N.card ≤ d + T := by
  have hbase := published_add_new_card_le_base hnew
  omega

/-! ## Simultaneous orthonormal extension -/

/-- Install all newly exposed coordinates at once.  `old` contains the
already published base columns and `query` contains `x⁰,…,xᵗ`.  The returned
list has exactly `|N|` directions, its concatenation with `old` is
orthonormal, and every new direction is orthogonal to every query through
the current round. -/
theorem exists_batch_orthogonal_extension {d T t : Nat}
    {I N : Finset (Fin d)}
    (old : List (EVector (d + T)))
    (query : Fin (t + 1) → EVector (d + T))
    (holdLength : old.length = I.card)
    (hold : WeaklyConvexLowerBound.Foundation.IsOrthonormalList old)
    (hnew : N ⊆ Iᶜ) (ht : t < T) :
    ∃ added : List (EVector (d + T)),
      added.length = N.card ∧
      WeaklyConvexLowerBound.Foundation.IsOrthonormalList (old ++ added) ∧
      ∀ u ∈ added, ∀ s : Fin (t + 1),
        WeaklyConvexLowerBound.Foundation.evecDotValue (query s) u = 0 := by
  let q : List (EVector (d + T)) := List.ofFn query
  have hqLength : q.length = t + 1 := by simp [q]
  have hcapacity : old.length + q.length + N.card ≤ d + T := by
    rw [holdLength, hqLength]
    exact batch_dimension_budget hnew ht
  obtain ⟨added, haddedLength, horth, havoid⟩ :=
    hold.complete_avoiding_right hcapacity
  refine ⟨added, haddedLength, horth, ?_⟩
  intro u hu s
  exact havoid u hu (query s) (by
    apply List.mem_ofFn.mpr
    exact ⟨s, rfl⟩)

/-- Frame-indexed form of the preceding theorem.  It records directly that
every current query projects to zero on every newly installed direction. -/
theorem exists_batch_extension_with_zero_projection {d T t : Nat}
    {I N : Finset (Fin d)}
    (old : List (EVector (d + T)))
    (query : Fin (t + 1) → EVector (d + T))
    (holdLength : old.length = I.card)
    (hold : WeaklyConvexLowerBound.Foundation.IsOrthonormalList old)
    (hnew : N ⊆ Iᶜ) (ht : t < T) :
    ∃ added : List (EVector (d + T)),
      added.length = N.card ∧
      WeaklyConvexLowerBound.Foundation.IsOrthonormalList (old ++ added) ∧
      ∀ s : Fin (t + 1),
        WeaklyConvexLowerBound.Foundation.frameProject (fun j : Fin added.length => added.get j)
          (query s) = 0 := by
  obtain ⟨added, hlen, horth, hzero⟩ :=
    exists_batch_orthogonal_extension old query holdLength hold hnew ht
  refine ⟨added, hlen, horth, ?_⟩
  intro s
  funext j
  unfold WeaklyConvexLowerBound.Foundation.frameProject
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm]
  exact hzero (added.get j) (List.get_mem added j) s

/-! ## A one-round invariant and the actual-transcript bridge -/

/-- The data retained by the batch construction immediately after a round.
The `reply` field is a genuine `FullOracleReply`: in particular, it retains
the entire set `reply.subdiff`. -/
structure BatchRoundState (d T t : Nat) where
  published : Finset (Fin d)
  direction : List (EVector (d + T))
  query : Fin (t + 1) → EVector (d + T)
  reply : FullOracleReply (d + T)
  direction_length : direction.length = published.card
  direction_orthonormal : WeaklyConvexLowerBound.Foundation.IsOrthonormalList direction

/-- One exact batch update.  `N` may be any finite set disjoint from the
published labels (in particular, the union support newly exposed by a full
set-valued reply).  Besides updating the cardinality invariant, the theorem
returns zero projection of every query through this round onto the whole new
batch. -/
theorem BatchRoundState.extend_batch {d T t : Nat}
    (S : BatchRoundState d T t)
    (N : Finset (Fin d)) (hnew : N ⊆ S.publishedᶜ) (ht : t < T) :
    ∃ added : List (EVector (d + T)),
      added.length = N.card ∧
      WeaklyConvexLowerBound.Foundation.IsOrthonormalList (S.direction ++ added) ∧
      (S.direction ++ added).length = (S.published ∪ N).card ∧
      ∀ s : Fin (t + 1),
        WeaklyConvexLowerBound.Foundation.frameProject (fun j : Fin added.length => added.get j)
          (S.query s) = 0 := by
  obtain ⟨added, hlen, horth, hzero⟩ :=
    exists_batch_extension_with_zero_projection S.direction S.query
      S.direction_length S.direction_orthonormal hnew ht
  have hdisj : Disjoint S.published N := by
    exact Finset.disjoint_left.2 fun i hiI hiN =>
      (Finset.mem_compl.1 (hnew hiN)) hiI
  refine ⟨added, hlen, horth, ?_, hzero⟩
  simp only [List.length_append, S.direction_length, hlen]
  exact (Finset.card_union_of_disjoint hdisj).symm

/-- Specialization in which `N` is computed from the union support of the
entire set-valued reply. -/
theorem BatchRoundState.extend_full_reply_support {d T t : Nat}
    (S : BatchRoundState d T t) (coordinate : Fin d → EVector (d + T))
    (ht : t < T) :
    ∃ added : List (EVector (d + T)),
      added.length = (newlyRevealedAlong coordinate S.published S.reply).card ∧
      WeaklyConvexLowerBound.Foundation.IsOrthonormalList (S.direction ++ added) ∧
      (S.direction ++ added).length =
        (S.published ∪ newlyRevealedAlong coordinate S.published S.reply).card ∧
      ∀ s : Fin (t + 1),
        WeaklyConvexLowerBound.Foundation.frameProject (fun j : Fin added.length => added.get j)
          (S.query s) = 0 := by
  exact S.extend_batch (newlyRevealedAlong coordinate S.published S.reply)
    (newlyRevealedAlong_subset_compl coordinate S.published S.reply) ht

/-- Extensional equality of the complete value/set replies is enough to turn
a causal synthetic table into the algorithm's actual recursively generated
queries.  In particular, this theorem never assumes equality for one chosen
subgradient. -/
theorem causal_full_set_table_eq_actual_queries {D K : Nat}
    {A : DeterministicFullOracleComponent D}
    {P : FullOracleProblem D}
    {query : Fin K → EVector D} {reply : Fin K → FullOracleReply D}
    (hcausal : BatchIsCausalTable A query reply)
    (hvalue : ∀ t, (reply t).value = P.objective (query t))
    (hfullSet : ∀ t, (reply t).subdiff = P.subdiff (query t)) :
    (∀ t : Fin K,
      DeterministicFullOracleComponent.queriedAt A P t.1 = query t) ∧
      DeterministicFullOracleComponent.queriedTranscript A P K = reply := by
  have hexact : ∀ t, reply t = fullOracle P (query t) := by
    intro t
    rcases hr : reply t with ⟨v, S⟩
    change FullOracleReply.mk v S =
      FullOracleReply.mk (P.objective (query t)) (P.subdiff (query t))
    congr
    · simpa [hr] using hvalue t
    · simpa [hr] using hfullSet t
  have hquery : ∀ t : Fin K,
      DeterministicFullOracleComponent.queriedAt A P t.1 = query t := by
    have hmain : ∀ n : Nat, ∀ hn : n < K,
        DeterministicFullOracleComponent.queriedAt A P n = query ⟨n, hn⟩ := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro hn
          rw [DeterministicFullOracleComponent.queriedAt_eq_nextQuery]
          rw [hcausal ⟨n, hn⟩]
          congr 1
          funext i
          unfold DeterministicFullOracleComponent.queriedTranscript
            DeterministicFullOracleComponent.replyAt batchTablePrefix
          let k : Fin K := ⟨i.1, by omega⟩
          have hi := ih i.1 i.2 (by omega)
          change fullOracle P
              (DeterministicFullOracleComponent.queriedAt A P i.1) = reply k
          rw [hi]
          exact (hexact k).symm
    intro t
    exact hmain t.1 t.2
  refine ⟨hquery, ?_⟩
  funext t
  unfold DeterministicFullOracleComponent.queriedTranscript
    DeterministicFullOracleComponent.replyAt
  rw [hquery t, ← hexact t]

/-! ## Labelled published frames -/

/-- Orthonormality restricted to a finite set of labelled base columns. -/
def IsOrthonormalOn {d D : Nat} (I : Finset (Fin d))
    (U : Fin d → EVector D) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I →
    WeaklyConvexLowerBound.Foundation.evecDotValue (U i) (U j) =
      if i = j then 1 else 0

/-- A partially revealed labelled frame in the fixed ambient space
`ℝ^(d+T)`.  Not-yet-revealed columns are represented by zero. -/
structure PublishedFrame (d T : Nat) where
  published : Finset (Fin d)
  column : Fin d → EVector (d + T)
  zero_of_not_mem : ∀ i, i ∉ published → column i = 0
  orthonormal_on : IsOrthonormalOn published column

def PublishedFrame.empty (d T : Nat) : PublishedFrame d T where
  published := ∅
  column := 0
  zero_of_not_mem := by simp
  orthonormal_on := by simp [IsOrthonormalOn]

/-- Projection onto all base labels, with currently hidden labels evaluating
to zero. -/
def PublishedFrame.project {d T : Nat} (F : PublishedFrame d T)
    (X : EVector (d + T)) : EVector d :=
  fun i => WeaklyConvexLowerBound.Foundation.evecDotValue (F.column i) X

@[simp] theorem PublishedFrame.project_zero {d T : Nat}
    (F : PublishedFrame d T) :
    F.project (0 : EVector (d + T)) = 0 := by
  funext i
  simp [PublishedFrame.project, WeaklyConvexLowerBound.Foundation.evecDotValue]

/-- Embed a base vector using the columns currently published. -/
def PublishedFrame.embed {d T : Nat} (F : PublishedFrame d T)
    (g : EVector d) : EVector (d + T) :=
  fun k => ∑ i : Fin d, g i * F.column i k

def finsetFrameList {d D : Nat} (I : Finset (Fin d))
    (U : Fin d → EVector D) : List (EVector D) :=
  List.ofFn fun k : Fin I.card =>
    U ((Finset.orderIsoOfFin I rfl) k).1

@[simp] theorem finsetFrameList_length {d D : Nat}
    (I : Finset (Fin d)) (U : Fin d → EVector D) :
    (finsetFrameList I U).length = I.card := by
  simp [finsetFrameList]

theorem isOrthonormalList_finsetFrameList {d D : Nat}
    {I : Finset (Fin d)} {U : Fin d → EVector D}
    (hU : IsOrthonormalOn I U) :
    WeaklyConvexLowerBound.Foundation.IsOrthonormalList (finsetFrameList I U) := by
  constructor
  · intro u hu
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
    simpa using hU _ ((Finset.orderIsoOfFin I rfl) k).2 _
      ((Finset.orderIsoOfFin I rfl) k).2
  · rw [List.pairwise_iff_get]
    intro i j hij
    let ii : Fin I.card := ⟨i.1, by
      simpa [finsetFrameList] using i.2⟩
    let jj : Fin I.card := ⟨j.1, by
      simpa [finsetFrameList] using j.2⟩
    have hiij : ii < jj := by exact hij
    have hne :
        ((Finset.orderIsoOfFin I rfl) ii).1 ≠
          ((Finset.orderIsoOfFin I rfl) jj).1 := by
      intro h
      have hsub : (Finset.orderIsoOfFin I rfl) ii =
          (Finset.orderIsoOfFin I rfl) jj := Subtype.ext h
      exact (ne_of_lt hiij) ((Finset.orderIsoOfFin I rfl).injective hsub)
    have hdot := hU _ ((Finset.orderIsoOfFin I rfl) ii).2 _
      ((Finset.orderIsoOfFin I rfl) jj).2
    rw [if_neg hne] at hdot
    simp only [finsetFrameList, List.get_ofFn]
    change WeaklyConvexLowerBound.Foundation.evecDotValue
      (U ((Finset.orderIsoOfFin I rfl) ii).1)
      (U ((Finset.orderIsoOfFin I rfl) jj).1) = 0
    exact hdot

/-- Generic form of the dimension count, with `k≤T` query constraints. -/
theorem batch_dimension_budget_of_query_count {d T k : Nat}
    {I N : Finset (Fin d)} (hnew : N ⊆ Iᶜ) (hk : k ≤ T) :
    I.card + k + N.card ≤ d + T := by
  have hbase := published_add_new_card_le_base hnew
  omega

private def assignedAddedColumn {d D : Nat} (N : Finset (Fin d))
    (added : List (EVector D)) (hlen : added.length = N.card)
    (i : N) : EVector D :=
  added.get (Fin.cast hlen.symm
    ((Finset.orderIsoOfFin N rfl).symm i))

/-- The certified result of installing a batch of labelled columns. -/
structure PublishedFrameBatchExtension {d T k : Nat}
    (F : PublishedFrame d T) (N : Finset (Fin d))
    (query : Fin k → EVector (d + T)) where
  next : PublishedFrame d T
  published_eq : next.published = F.published ∪ N
  keeps_old : ∀ i, i ∈ F.published → next.column i = F.column i
  keeps_outside_new : ∀ i, i ∉ N → next.column i = F.column i
  new_query_orthogonal : ∀ i, i ∈ N → ∀ s,
    WeaklyConvexLowerBound.Foundation.evecDotValue (next.column i) (query s) = 0
  project_preserved : ∀ s, next.project (query s) = F.project (query s)

/-- Labelled simultaneous extension.  Unlike the older one-direction lemma,
this theorem installs every coordinate of `N` in one step. -/
theorem exists_labelled_batch_extension {d T k : Nat}
    (F : PublishedFrame d T) (N : Finset (Fin d))
    (query : Fin k → EVector (d + T))
    (hnew : N ⊆ F.publishedᶜ) (hk : k ≤ T) :
    Nonempty (PublishedFrameBatchExtension F N query) := by
  classical
  let old := finsetFrameList F.published F.column
  let q : List (EVector (d + T)) := List.ofFn query
  have hold : WeaklyConvexLowerBound.Foundation.IsOrthonormalList old := by
    exact isOrthonormalList_finsetFrameList F.orthonormal_on
  have hcapacity : old.length + q.length + N.card ≤ d + T := by
    simp only [old, q, finsetFrameList_length, List.length_ofFn]
    exact batch_dimension_budget_of_query_count hnew hk
  obtain ⟨added, haddedLength, hall, havoid⟩ :=
    hold.complete_avoiding_right hcapacity
  let newColumn : Fin d → EVector (d + T) := fun i =>
    if hi : i ∈ N then
      assignedAddedColumn N added haddedLength ⟨i, hi⟩
    else F.column i
  have hpair := List.pairwise_append.mp hall.2
  have haddedList : WeaklyConvexLowerBound.Foundation.IsOrthonormalList added := by
    constructor
    · intro u hu
      exact hall.1 u (List.mem_append_right old hu)
    · exact hpair.2.1
  have haddedFrame := haddedList.get_frame
  have hcross := hpair.2.2
  let Fnext : PublishedFrame d T := {
    published := F.published ∪ N
    column := newColumn
    zero_of_not_mem := by
      intro i hi
      have hiN : i ∉ N := by
        intro hiN
        exact hi (Finset.mem_union_right _ hiN)
      have hiI : i ∉ F.published := by
        intro hiI
        exact hi (Finset.mem_union_left _ hiI)
      simp [newColumn, hiN, F.zero_of_not_mem i hiI]
    orthonormal_on := by
      intro i hi j hj
      have hiCases := Finset.mem_union.mp hi
      have hjCases := Finset.mem_union.mp hj
      by_cases hiN : i ∈ N
      · by_cases hjN : j ∈ N
        · let ai : Fin added.length := Fin.cast haddedLength.symm
            ((Finset.orderIsoOfFin N rfl).symm ⟨i, hiN⟩)
          let aj : Fin added.length := Fin.cast haddedLength.symm
            ((Finset.orderIsoOfFin N rfl).symm ⟨j, hjN⟩)
          by_cases hij : i = j
          · subst j
            have hself := haddedFrame ai ai
            rw [if_pos rfl] at hself
            simpa [newColumn, hiN, assignedAddedColumn, ai] using hself
          · have haij : ai ≠ aj := by
              intro ha
              have hfin :
                  (Finset.orderIsoOfFin N rfl).symm ⟨i, hiN⟩ =
                    (Finset.orderIsoOfFin N rfl).symm ⟨j, hjN⟩ := by
                apply Fin.ext
                have hv : ai.val = aj.val :=
                  congrArg (fun z : Fin added.length => z.val) ha
                simpa [ai, aj] using hv
              have hsub : (⟨i, hiN⟩ : N) = ⟨j, hjN⟩ := by
                exact (Finset.orderIsoOfFin N rfl).symm.injective hfin
              exact hij (congrArg Subtype.val hsub)
            have hdiff := haddedFrame ai aj
            rw [if_neg haij] at hdiff
            simpa [newColumn, hiN, hjN, hij, assignedAddedColumn, ai, aj]
              using hdiff
        · have hjI : j ∈ F.published := hjCases.resolve_right hjN
          have hiIneg : i ∉ F.published := by
            intro hiI
            exact (Finset.mem_compl.1 (hnew hiN)) hiI
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hiIneg hjI
          let ai : Fin added.length := Fin.cast haddedLength.symm
            ((Finset.orderIsoOfFin N rfl).symm ⟨i, hiN⟩)
          have hOldMem : F.column j ∈ old := by
            apply List.mem_ofFn.mpr
            refine ⟨(Finset.orderIsoOfFin F.published rfl).symm ⟨j, hjI⟩, ?_⟩
            simp
          have hNewMem : added.get ai ∈ added := List.get_mem added ai
          have hc := hcross (F.column j) hOldMem (added.get ai) hNewMem
          rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm] at hc
          simpa [newColumn, hiN, hjN, hij, assignedAddedColumn, ai] using hc
      · have hiI : i ∈ F.published := hiCases.resolve_right hiN
        by_cases hjN : j ∈ N
        · have hjIneg : j ∉ F.published := by
            intro hjI
            exact (Finset.mem_compl.1 (hnew hjN)) hjI
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hjIneg hiI
          let aj : Fin added.length := Fin.cast haddedLength.symm
            ((Finset.orderIsoOfFin N rfl).symm ⟨j, hjN⟩)
          have hOldMem : F.column i ∈ old := by
            apply List.mem_ofFn.mpr
            refine ⟨(Finset.orderIsoOfFin F.published rfl).symm ⟨i, hiI⟩, ?_⟩
            simp
          have hNewMem : added.get aj ∈ added := List.get_mem added aj
          have hc := hcross (F.column i) hOldMem (added.get aj) hNewMem
          simpa [newColumn, hiN, hjN, hij, assignedAddedColumn, aj] using hc
        · have hjI : j ∈ F.published := hjCases.resolve_right hjN
          simpa [newColumn, hiN, hjN] using
            F.orthonormal_on i hiI j hjI
  }
  refine ⟨{
    next := Fnext
    published_eq := rfl
    keeps_old := ?_
    keeps_outside_new := ?_
    new_query_orthogonal := ?_
    project_preserved := ?_
  }⟩
  · intro i hiI
    have hiN : i ∉ N := by
      intro hiN
      exact (Finset.mem_compl.1 (hnew hiN)) hiI
    simp [Fnext, newColumn, hiN]
  · intro i hiN
    simp [Fnext, newColumn, hiN]
  · intro i hiN s
    let ai : Fin added.length := Fin.cast haddedLength.symm
      ((Finset.orderIsoOfFin N rfl).symm ⟨i, hiN⟩)
    have hz := havoid (added.get ai) (List.get_mem added ai)
      (query s) (by
        apply List.mem_ofFn.mpr
        exact ⟨s, rfl⟩)
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm] at hz
    simpa [Fnext, newColumn, hiN, assignedAddedColumn, ai] using hz
  · intro s
    funext i
    unfold PublishedFrame.project
    by_cases hiN : i ∈ N
    · have hFold : F.column i = 0 :=
        F.zero_of_not_mem i (Finset.mem_compl.1 (hnew hiN))
      have hz : WeaklyConvexLowerBound.Foundation.evecDotValue (Fnext.column i) (query s) = 0 := by
        let ai : Fin added.length := Fin.cast haddedLength.symm
          ((Finset.orderIsoOfFin N rfl).symm ⟨i, hiN⟩)
        have hza := havoid (added.get ai) (List.get_mem added ai)
          (query s) (by
            apply List.mem_ofFn.mpr
            exact ⟨s, rfl⟩)
        rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm] at hza
        simpa [Fnext, newColumn, hiN, assignedAddedColumn, ai] using hza
      rw [hz, hFold]
      simp [WeaklyConvexLowerBound.Foundation.evecDotValue]
    · simp [Fnext, newColumn, hiN]

/-! ## Synthetic full-set replies and dynamic states -/

/-- Rotate a complete base reply through the currently published frame.  Its
subdifferential field is the image of the *entire* base set. -/
def rotateBaseReply {d T : Nat} (F : PublishedFrame d T)
    (r : FullOracleReply d) : FullOracleReply (d + T) where
  value := r.value
  subdiff := F.embed '' r.subdiff

theorem PublishedFrame.embed_eq_of_columns_outside {d T : Nat}
    (F G : PublishedFrame d T) (N : Finset (Fin d))
    (hcolumn : ∀ i, i ∉ N → G.column i = F.column i)
    {g : EVector d} (hzero : ∀ i, i ∈ N → g i = 0) :
    G.embed g = F.embed g := by
  funext k
  unfold PublishedFrame.embed
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ N
  · rw [hzero i hi]
    simp
  · rw [hcolumn i hi]

theorem rotateBaseReply_eq_of_support_avoids {d T : Nat}
    (F G : PublishedFrame d T) (N : Finset (Fin d))
    (hcolumn : ∀ i, i ∉ N → G.column i = F.column i)
    (r : FullOracleReply d)
    (havoid : ∀ i, i ∈ N → i ∉ fullReplyCoordinateSupport r) :
    rotateBaseReply G r = rotateBaseReply F r := by
  have hembed : ∀ g ∈ r.subdiff, G.embed g = F.embed g := by
    intro g hg
    apply PublishedFrame.embed_eq_of_columns_outside F G N hcolumn
    intro i hi
    by_contra hgi
    exact havoid i hi (mem_fullReplyCoordinateSupport_iff.2 ⟨g, hg, hgi⟩)
  cases r with
  | mk value subdiff =>
      apply congrArg (fun S : Set (EVector (d + T)) =>
        FullOracleReply.mk value S)
      ext v
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, hg, (hembed g hg).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, hg, hembed g hg⟩

private theorem extend_batch_causal_table {D n : Nat}
    {A : DeterministicFullOracleComponent D}
    {query : Fin n → EVector D} {reply : Fin n → FullOracleReply D}
    (hcausal : BatchIsCausalTable A query reply)
    (x : EVector D) (hx : x = A.nextQuery n reply)
    (r : FullOracleReply D) :
    BatchIsCausalTable A (Fin.lastCases x query) (Fin.lastCases r reply) := by
  intro t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · simp only [Fin.lastCases_last, Fin.val_last]
    change x = A.nextQuery n
      (batchTablePrefix (Fin.lastCases r reply) (Fin.last n))
    rw [hx]
    congr 1
    funext j
    change reply j = Fin.lastCases r reply ⟨j.1, by omega⟩
    have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc j := Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]
  · simp only [Fin.lastCases_castSucc, Fin.val_castSucc]
    change query i = A.nextQuery i.1
      (batchTablePrefix (Fin.lastCases r reply) (Fin.castSucc i))
    rw [hcausal i]
    congr 1
    funext j
    let k : Fin n := ⟨j.1, by omega⟩
    change reply k = Fin.lastCases r reply ⟨j.1, by omega⟩
    have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc k := Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]

/-- State after `n` complete rounds of the batch resisting construction. -/
structure DynamicBatchState (d T n : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (baseOracle : EVector d → FullOracleReply d) where
  frame : PublishedFrame d T
  query : Fin n → EVector (d + T)
  baseQuery : Fin n → EVector d
  baseReply : Fin n → FullOracleReply d
  reply : Fin n → FullOracleReply (d + T)
  causal : BatchIsCausalTable A query reply
  baseQuery_eq_project : ∀ s, baseQuery s = frame.project (query s)
  baseReply_eq : ∀ s, baseReply s = baseOracle (baseQuery s)
  reply_eq_rotated : ∀ s, reply s = rotateBaseReply frame (baseReply s)
  support_published : ∀ s i,
    i ∈ fullReplyCoordinateSupport (baseReply s) → i ∈ frame.published
  published_has_origin : ∀ i, i ∈ frame.published →
    ∃ s : Fin n, i ∈ fullReplyCoordinateSupport (baseReply s)
  base_zero_respecting : ∀ s i, baseQuery s i ≠ 0 →
    ∃ r : Fin n, r.1 < s.1 ∧
      i ∈ fullReplyCoordinateSupport (baseReply r)

def DynamicBatchState.initial (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (baseOracle : EVector d → FullOracleReply d) :
    DynamicBatchState d T 0 A baseOracle where
  frame := PublishedFrame.empty d T
  query := Fin.elim0
  baseQuery := Fin.elim0
  baseReply := Fin.elim0
  reply := Fin.elim0
  causal := by intro i; exact Fin.elim0 i
  baseQuery_eq_project := by intro i; exact Fin.elim0 i
  baseReply_eq := by intro i; exact Fin.elim0 i
  reply_eq_rotated := by intro i; exact Fin.elim0 i
  support_published := by intro i; exact Fin.elim0 i
  published_has_origin := by
    intro i hi
    simp [PublishedFrame.empty] at hi
  base_zero_respecting := by intro i; exact Fin.elim0 i

/-- Perform one complete adaptive round.  The current query is fixed by the
old full replies, the base oracle is evaluated at its current projection,
the union support of that whole base set determines `N`, and all columns in
`N` are installed before the synthetic full-set reply is returned. -/
theorem DynamicBatchState.exists_next {d T n : Nat}
    {A : DeterministicFullOracleComponent (d + T)}
    {baseOracle : EVector d → FullOracleReply d}
    (S : DynamicBatchState d T n A baseOracle) (hn : n < T) :
    Nonempty (DynamicBatchState d T (n + 1) A baseOracle) := by
  classical
  let x : EVector (d + T) := A.nextQuery n S.reply
  let queryNext : Fin (n + 1) → EVector (d + T) :=
    Fin.lastCases x S.query
  let z : EVector d := S.frame.project x
  let b : FullOracleReply d := baseOracle z
  let N : Finset (Fin d) :=
    fullReplyCoordinateSupport b \ S.frame.published
  have hnew : N ⊆ S.frame.publishedᶜ := by
    intro i hi
    exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hi).2
  have hk : n + 1 ≤ T := by omega
  let E := Classical.choice
    (exists_labelled_batch_extension S.frame N queryNext hnew hk)
  let frameNext : PublishedFrame d T := E.next
  let r : FullOracleReply (d + T) := rotateBaseReply frameNext b
  let baseQueryNext : Fin (n + 1) → EVector d :=
    Fin.lastCases z S.baseQuery
  let baseReplyNext : Fin (n + 1) → FullOracleReply d :=
    Fin.lastCases b S.baseReply
  let replyNext : Fin (n + 1) → FullOracleReply (d + T) :=
    Fin.lastCases r S.reply
  refine ⟨{
    frame := frameNext
    query := queryNext
    baseQuery := baseQueryNext
    baseReply := baseReplyNext
    reply := replyNext
    causal := ?_
    baseQuery_eq_project := ?_
    baseReply_eq := ?_
    reply_eq_rotated := ?_
    support_published := ?_
    published_has_origin := ?_
    base_zero_respecting := ?_
  }⟩
  · exact extend_batch_causal_table S.causal x rfl r
  · intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · simp only [baseQueryNext, queryNext, Fin.lastCases_last]
      simpa [z, frameNext, queryNext] using
        (E.project_preserved (Fin.last n)).symm
    · simp only [baseQueryNext, queryNext, Fin.lastCases_castSucc]
      rw [S.baseQuery_eq_project i]
      simpa [frameNext, queryNext] using
        (E.project_preserved (Fin.castSucc i)).symm
  · intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · simp [baseReplyNext, baseQueryNext, b]
    · simp only [baseReplyNext, baseQueryNext, Fin.lastCases_castSucc]
      exact S.baseReply_eq i
  · intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · simp [replyNext, baseReplyNext, r]
    · simp only [replyNext, baseReplyNext, Fin.lastCases_castSucc]
      have havoidOld : ∀ j, j ∈ N →
          j ∉ fullReplyCoordinateSupport (S.baseReply i) := by
        intro j hjN hjSupport
        have hjOld : j ∈ S.frame.published :=
          S.support_published i j hjSupport
        exact (Finset.mem_sdiff.1 hjN).2 hjOld
      have hrot := rotateBaseReply_eq_of_support_avoids
        S.frame frameNext N E.keeps_outside_new (S.baseReply i) havoidOld
      exact (S.reply_eq_rotated i).trans hrot.symm
  · intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · intro j hj
      have hj' : j ∈ fullReplyCoordinateSupport b := by
        simpa [baseReplyNext] using hj
      change j ∈ frameNext.published
      rw [E.published_eq]
      by_cases hjOld : j ∈ S.frame.published
      · exact Finset.mem_union_left N hjOld
      · apply Finset.mem_union_right
        exact Finset.mem_sdiff.2 ⟨hj', hjOld⟩
    · intro j hj
      have hj' : j ∈ fullReplyCoordinateSupport (S.baseReply i) := by
        simpa [baseReplyNext] using hj
      change j ∈ frameNext.published
      rw [E.published_eq]
      exact Finset.mem_union_left N (S.support_published i j hj')
  · intro j hj
    change j ∈ frameNext.published at hj
    rw [E.published_eq] at hj
    rcases Finset.mem_union.mp hj with hjOld | hjNew
    · obtain ⟨s, hs⟩ := S.published_has_origin j hjOld
      refine ⟨Fin.castSucc s, ?_⟩
      simpa [baseReplyNext] using hs
    · have hjSupport : j ∈ fullReplyCoordinateSupport b :=
        (Finset.mem_sdiff.1 hjNew).1
      refine ⟨Fin.last n, ?_⟩
      simpa [baseReplyNext] using hjSupport
  · intro s
    refine Fin.lastCases ?_ (fun q => ?_) s
    · intro i hzi
      have hzi' : z i ≠ 0 := by
        simpa [baseQueryNext] using hzi
      have hiOld : i ∈ S.frame.published := by
        by_contra hi
        have hcol := S.frame.zero_of_not_mem i hi
        unfold z PublishedFrame.project at hzi'
        rw [hcol] at hzi'
        simp [WeaklyConvexLowerBound.Foundation.evecDotValue] at hzi'
      obtain ⟨rOld, hrSupport⟩ := S.published_has_origin i hiOld
      refine ⟨Fin.castSucc rOld, ?_, ?_⟩
      · simp only [Fin.val_castSucc, Fin.val_last]
        exact rOld.isLt
      · simpa [baseReplyNext] using hrSupport
    · intro i hqi
      have hqi' : S.baseQuery q i ≠ 0 := by
        simpa [baseQueryNext] using hqi
      obtain ⟨rOld, hrlt, hrSupport⟩ := S.base_zero_respecting q i hqi'
      refine ⟨Fin.castSucc rOld, ?_, ?_⟩
      · simpa using hrlt
      · simpa [baseReplyNext] using hrSupport

/-- Iterate the batch update through all `T` rounds in the fixed space
`ℝ^(d+T)`. -/
theorem exists_dynamicBatchState (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (baseOracle : EVector d → FullOracleReply d) :
    Nonempty (DynamicBatchState d T T A baseOracle) := by
  have build : ∀ n : Nat, n ≤ T →
      Nonempty (DynamicBatchState d T n A baseOracle) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨DynamicBatchState.initial d T A baseOracle⟩
    | succ n ih =>
        intro hn
        have hnlt : n < T := by omega
        let S := Classical.choice (ih (by omega))
        exact S.exists_next hnlt
  exact build T le_rfl

/-- A `T`-round dynamic table whose remaining base columns have been
orthogonally completed.  The adaptive state remembers only genuinely
revealed indices; `finalFrame` additionally contains the unrevealed
completion columns. -/
structure CompletedDynamicBatchTable (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (baseOracle : EVector d → FullOracleReply d) where
  adaptive : DynamicBatchState d T T A baseOracle
  finalFrame : PublishedFrame d T
  frame_complete : finalFrame.published = Finset.univ
  final_project : ∀ s,
    adaptive.baseQuery s = finalFrame.project (adaptive.query s)
  final_reply_rotated : ∀ s,
    adaptive.reply s = rotateBaseReply finalFrame (adaptive.baseReply s)

theorem CompletedDynamicBatchTable.frame_orthonormal {d T : Nat}
    {A : DeterministicFullOracleComponent (d + T)}
    {baseOracle : EVector d → FullOracleReply d}
    (C : CompletedDynamicBatchTable d T A baseOracle) :
    WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame C.finalFrame.column := by
  intro i j
  apply C.finalFrame.orthonormal_on i
  · rw [C.frame_complete]
    exact Finset.mem_univ i
  · rw [C.frame_complete]
    exact Finset.mem_univ j

/-- After the adaptive rounds, install all remaining base coordinates at
once while avoiding all `T` queries.  The exact capacity is
`d + T`, with equality allowed. -/
theorem exists_completedDynamicBatchTable (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (baseOracle : EVector d → FullOracleReply d) :
    Nonempty (CompletedDynamicBatchTable d T A baseOracle) := by
  classical
  let S := Classical.choice (exists_dynamicBatchState d T A baseOracle)
  let remaining : Finset (Fin d) := S.frame.publishedᶜ
  have hremaining : remaining ⊆ S.frame.publishedᶜ := Finset.Subset.rfl
  let E := Classical.choice
    (exists_labelled_batch_extension S.frame remaining S.query
      hremaining le_rfl)
  let finalFrame := E.next
  have hcomplete : finalFrame.published = Finset.univ := by
    rw [show finalFrame.published = S.frame.published ∪ remaining from
      E.published_eq]
    simp [remaining]
  refine ⟨{
    adaptive := S
    finalFrame := finalFrame
    frame_complete := hcomplete
    final_project := ?_
    final_reply_rotated := ?_
  }⟩
  · intro s
    rw [S.baseQuery_eq_project s]
    exact (E.project_preserved s).symm
  · intro s
    have havoidRemaining : ∀ i, i ∈ remaining →
        i ∉ fullReplyCoordinateSupport (S.baseReply s) := by
      intro i hiRemaining hiSupport
      have hiPublished := S.support_published s i hiSupport
      exact (Finset.mem_compl.1 hiRemaining) hiPublished
    have hrot := rotateBaseReply_eq_of_support_avoids
      S.frame finalFrame remaining E.keeps_outside_new
        (S.baseReply s) havoidRemaining
    exact (S.reply_eq_rotated s).trans hrot.symm

theorem BatchIsCausalTable.first_query_zero {D K : Nat}
    {A : DeterministicFullOracleComponent D}
    {query : Fin K → EVector D} {reply : Fin K → FullOracleReply D}
    (hcausal : BatchIsCausalTable A query reply) (hK : 0 < K) :
    query ⟨0, hK⟩ = 0 := by
  have h := hcausal ⟨0, hK⟩
  change query ⟨0, hK⟩ = A.nextQuery 0
    (batchTablePrefix reply ⟨0, hK⟩) at h
  rw [show batchTablePrefix reply ⟨0, hK⟩ = emptyFullHistory D from
    Subsingleton.elim _ _] at h
  exact h.trans A.initial_query

/-- Extend the finite projected base queries by zero after the horizon, as
required by the manuscript's `Nat`-indexed zero-respecting definition. -/
def CompletedDynamicBatchTable.blockQuery {M N T : Nat}
    {A : DeterministicFullOracleComponent (M * N + T)}
    {baseOracle : EVector (M * N) → FullOracleReply (M * N)}
    (C : CompletedDynamicBatchTable (M * N) T A baseOracle)
    (t : Nat) : BlockVec M N :=
  if ht : t < T then unflatten (C.adaptive.baseQuery ⟨t, ht⟩) else 0

/-- The projected base sequence is genuinely full-set zero-respecting.  The
hypothesis identifies the complete base reply set with the target block
oracle; no representative vector is selected. -/
theorem CompletedDynamicBatchTable.blockQuery_fullSetZeroRespecting
    {M N T : Nat}
    {A : DeterministicFullOracleComponent (M * N + T)}
    {baseOracle : EVector (M * N) → FullOracleReply (M * N)}
    (C : CompletedDynamicBatchTable (M * N) T A baseOracle)
    (oracle : BlockVec M N → Set (BlockVec M N))
    (hbaseFullSet : ∀ z,
      (baseOracle (flatten z)).subdiff = flatten '' oracle z) :
    FullSetZeroRespecting oracle C.blockQuery := by
  constructor
  · unfold CompletedDynamicBatchTable.blockQuery
    by_cases hT : 0 < T
    · simp only [hT, ↓reduceDIte]
      have hq0 := C.adaptive.causal.first_query_zero hT
      have hp0 := C.final_project ⟨0, hT⟩
      rw [hq0] at hp0
      rw [PublishedFrame.project_zero] at hp0
      rw [hp0]
      exact unflatten_zero
    · have : ¬ 0 < T := hT
      simp [this]
  · intro t p hnonzero
    unfold CompletedDynamicBatchTable.blockQuery at hnonzero
    split at hnonzero
    next ht =>
      let s : Fin T := ⟨t, ht⟩
      let i : Fin (M * N) := finProdFinEquiv p
      have hcoord : C.adaptive.baseQuery s i ≠ 0 := by
        simpa [s, i, unflatten] using hnonzero
      obtain ⟨r, hrt, hrSupport⟩ :=
        C.adaptive.base_zero_respecting s i hcoord
      obtain ⟨g, hg, hgi⟩ :=
        mem_fullReplyCoordinateSupport_iff.1 hrSupport
      refine ⟨r.1, hrt, ?_⟩
      have hreply := C.adaptive.baseReply_eq r
      have hflat : C.adaptive.baseQuery r =
          flatten (unflatten (C.adaptive.baseQuery r)) := by
        rw [flatten_unflatten]
      have hg' : g ∈
          (baseOracle (flatten
            (unflatten (C.adaptive.baseQuery r)))).subdiff := by
        rw [← hflat, ← hreply]
        exact hg
      rw [hbaseFullSet] at hg'
      obtain ⟨gb, hgb, hgbflat⟩ := hg'
      refine ⟨gb, ?_, ?_⟩
      · simpa [CompletedDynamicBatchTable.blockQuery, r.isLt] using hgb
      have hcoordEq := congrFun hgbflat i
      have hflatCoord : flatten gb i = gb p.1 p.2 := by
        simp [i, flatten]
      rw [← hcoordEq, hflatCoord] at hgi
      exact hgi
    next ht =>
      simp only [Pi.zero_apply] at hnonzero
      exact (hnonzero rfl).elim

/-- End-to-end bridge for the dynamic construction.  Once the concrete
rotated problem is proved to return exactly the full rotated set on the
synthetic queries, causality forces the synthetic table to be the actual
algorithmic transcript.  Simultaneously, projection through the completed
`d`-column frame is the block-valued `FullSetZeroRespecting` sequence. -/
theorem CompletedDynamicBatchTable.actual_transcript_and_fullSetZeroRespecting
    {M N T : Nat}
    {A : DeterministicFullOracleComponent (M * N + T)}
    {baseOracle : EVector (M * N) → FullOracleReply (M * N)}
    (C : CompletedDynamicBatchTable (M * N) T A baseOracle)
    (oracle : BlockVec M N → Set (BlockVec M N))
    (P : FullOracleProblem (M * N + T))
    (hbaseFullSet : ∀ z,
      (baseOracle (flatten z)).subdiff = flatten '' oracle z)
    (hrotatedFullSetIdentity : ∀ t,
      fullOracle P (C.adaptive.query t) =
        rotateBaseReply C.finalFrame
          (baseOracle (C.finalFrame.project (C.adaptive.query t)))) :
    DeterministicFullOracleComponent.queriedTranscript A P T =
        C.adaptive.reply ∧
      (∀ t : Fin T,
        DeterministicFullOracleComponent.queriedAt A P t.1 =
          C.adaptive.query t) ∧
      FullSetZeroRespecting oracle C.blockQuery ∧
      ∀ t : Fin T,
        C.blockQuery t.1 =
          unflatten (WeaklyConvexLowerBound.Foundation.frameProject C.finalFrame.column
            (DeterministicFullOracleComponent.queriedAt A P t.1)) := by
  have hexact : ∀ t,
      fullOracle P (C.adaptive.query t) = C.adaptive.reply t := by
    intro t
    calc
      fullOracle P (C.adaptive.query t) =
          rotateBaseReply C.finalFrame
            (baseOracle (C.finalFrame.project (C.adaptive.query t))) :=
        hrotatedFullSetIdentity t
      _ = rotateBaseReply C.finalFrame
          (baseOracle (C.adaptive.baseQuery t)) := by
        rw [C.final_project t]
      _ = rotateBaseReply C.finalFrame (C.adaptive.baseReply t) := by
        rw [C.adaptive.baseReply_eq t]
      _ = C.adaptive.reply t := (C.final_reply_rotated t).symm
  have hvalue : ∀ t,
      (C.adaptive.reply t).value = P.objective (C.adaptive.query t) := by
    intro t
    have h := congrArg FullOracleReply.value (hexact t).symm
    exact h
  have hfullSet : ∀ t,
      (C.adaptive.reply t).subdiff = P.subdiff (C.adaptive.query t) := by
    intro t
    have h := congrArg FullOracleReply.subdiff (hexact t).symm
    exact h
  obtain ⟨hquery, htranscript⟩ :=
    causal_full_set_table_eq_actual_queries C.adaptive.causal hvalue hfullSet
  refine ⟨htranscript, hquery,
    C.blockQuery_fullSetZeroRespecting oracle hbaseFullSet, ?_⟩
  intro t
  have hfinite : C.blockQuery t.1 =
      unflatten (C.adaptive.baseQuery t) := by
    simp [CompletedDynamicBatchTable.blockQuery, t.isLt]
  rw [hfinite, C.final_project t]
  rw [hquery t]
  rfl

end

end WeaklyConvexLowerBound


