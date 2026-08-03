import WeaklyConvexLowerBound.BatchResisting
import WeaklyConvexLowerBound.DeterministicAssembly

/-!
# A function-independent finite-horizon resisting transformation

`BatchResisting` constructs the correct adaptive table after a base oracle
has been fixed.  The manuscript states the stronger quantifier order in
which one low-dimensional, transcript-causal algorithm is fixed first and
then works for every base function.  This file implements that online
transformation: its state is recursively reconstructed from the supplied
finite reply history, so its definition contains no objective or oracle.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- The function-independent state after `n` low-dimensional replies.
Unlike `DynamicBatchState`, it stores the replies supplied in the transcript
and has no `baseOracle` parameter. -/
structure UniformBatchState (d T n : Nat)
    (A : DeterministicFullOracleComponent (d + T)) where
  frame : PublishedFrame d T
  query : Fin n → EVector (d + T)
  baseQuery : Fin n → EVector d
  baseReply : Fin n → FullOracleReply d
  reply : Fin n → FullOracleReply (d + T)
  causal : BatchIsCausalTable A query reply
  baseQuery_eq_project : ∀ s, baseQuery s = frame.project (query s)
  reply_eq_rotated : ∀ s, reply s = rotateBaseReply frame (baseReply s)
  support_published : ∀ s i,
    i ∈ fullReplyCoordinateSupport (baseReply s) → i ∈ frame.published
  published_has_origin : ∀ i, i ∈ frame.published →
    ∃ s : Fin n, i ∈ fullReplyCoordinateSupport (baseReply s)
  base_zero_respecting : ∀ s i, baseQuery s i ≠ 0 →
    ∃ r : Fin n, r.1 < s.1 ∧
      i ∈ fullReplyCoordinateSupport (baseReply r)

def UniformBatchState.initial (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T)) :
    UniformBatchState d T 0 A where
  frame := PublishedFrame.empty d T
  query := Fin.elim0
  baseQuery := Fin.elim0
  baseReply := Fin.elim0
  reply := Fin.elim0
  causal := by intro i; exact Fin.elim0 i
  baseQuery_eq_project := by intro i; exact Fin.elim0 i
  reply_eq_rotated := by intro i; exact Fin.elim0 i
  support_published := by intro i; exact Fin.elim0 i
  published_has_origin := by
    intro i hi
    simp [PublishedFrame.empty] at hi
  base_zero_respecting := by intro i; exact Fin.elim0 i

private theorem extend_uniform_batch_causal_table {D n : Nat}
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
    have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) =
        Fin.castSucc j := Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]
  · simp only [Fin.lastCases_castSucc, Fin.val_castSucc]
    change query i = A.nextQuery i.1
      (batchTablePrefix (Fin.lastCases r reply) (Fin.castSucc i))
    rw [hcausal i]
    congr 1
    funext j
    let k : Fin n := ⟨j.1, by omega⟩
    change reply k = Fin.lastCases r reply ⟨j.1, by omega⟩
    have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) =
        Fin.castSucc k := Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]

/-- One uniform online update.  The new base reply is an explicit argument,
so this operation is a deterministic function of the preceding state and
the next transcript entry. -/
def UniformBatchState.next {d T n : Nat}
    {A : DeterministicFullOracleComponent (d + T)}
    (S : UniformBatchState d T n A) (b : FullOracleReply d)
    (hn : n < T) : UniformBatchState d T (n + 1) A := by
  classical
  let x : EVector (d + T) := A.nextQuery n S.reply
  let queryNext : Fin (n + 1) → EVector (d + T) :=
    Fin.lastCases x S.query
  let z : EVector d := S.frame.project x
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
  refine {
    frame := frameNext
    query := queryNext
    baseQuery := baseQueryNext
    baseReply := baseReplyNext
    reply := replyNext
    causal := ?_
    baseQuery_eq_project := ?_
    reply_eq_rotated := ?_
    support_published := ?_
    published_has_origin := ?_
    base_zero_respecting := ?_ }
  · exact extend_uniform_batch_causal_table S.causal x rfl r
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
      obtain ⟨rOld, hrlt, hrSupport⟩ :=
        S.base_zero_respecting q i hqi'
      refine ⟨Fin.castSucc rOld, ?_, ?_⟩
      · simpa using hrlt
      · simpa [baseReplyNext] using hrSupport

def uniformHistoryPrefix {d n : Nat}
    (history : FullReplyHistory d (n + 1)) : FullReplyHistory d n :=
  fun i => history (Fin.castSucc i)

/-- Reconstruct the online state from exactly the supplied finite history.
The successor clause extends the recursively reconstructed prefix state,
which makes choices coherent on every branch of the transcript tree. -/
def uniformBatchStateFromHistory (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T)) :
    (n : Nat) → n ≤ T → FullReplyHistory d n → UniformBatchState d T n A
  | 0, _, _ => UniformBatchState.initial d T A
  | n + 1, hn, history =>
      let S := uniformBatchStateFromHistory d T A n (by omega)
        (uniformHistoryPrefix history)
      S.next (history (Fin.last n)) (by omega)

/-- The single low-dimensional causal component determined by the ambient
component and horizon.  Before the horizon it reconstructs the resisting
frame from its transcript; afterwards it queries zero. -/
def uniformZeroRespectingComponent (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T)) :
    DeterministicFullOracleComponent d where
  nextQuery := fun t history =>
    if ht : t < T then
      let S := uniformBatchStateFromHistory d T A t (Nat.le_of_lt ht) history
      S.frame.project (A.nextQuery t S.reply)
    else 0
  initial_query := by
    by_cases hT : 0 < T
    · simp only [hT, ↓reduceDIte]
      funext i
      simp [uniformBatchStateFromHistory, UniformBatchState.initial,
        PublishedFrame.project, PublishedFrame.empty,
        WeaklyConvexLowerBound.Foundation.evecDotValue]
    · simp [hT]
  output := fun _ _ => 0

theorem uniformBatchStateFromHistory_baseReply (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (n : Nat) (hn : n ≤ T) (history : FullReplyHistory d n) :
    (uniformBatchStateFromHistory d T A n hn history).baseReply = history := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [uniformBatchStateFromHistory, UniformBatchState.next]
      · simp only [uniformBatchStateFromHistory, UniformBatchState.next,
          Fin.lastCases_castSucc]
        exact congrFun
          (ih (by omega) (uniformHistoryPrefix history)) j

/-- The projected query table reconstructed from a history is causal for
the single low-dimensional component defined above. -/
theorem uniformBatchStateFromHistory_base_causal (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T))
    (n : Nat) (hn : n ≤ T) (history : FullReplyHistory d n) :
    BatchIsCausalTable (uniformZeroRespectingComponent d T A)
      (uniformBatchStateFromHistory d T A n hn history).baseQuery
      (uniformBatchStateFromHistory d T A n hn history).baseReply := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let histPrefix := uniformHistoryPrefix history
      let S := uniformBatchStateFromHistory d T A n (by omega) histPrefix
      let b := history (Fin.last n)
      have hnlt : n < T := by omega
      have hbase : S.baseReply = histPrefix := by
        exact uniformBatchStateFromHistory_baseReply
          d T A n (by omega) histPrefix
      intro t
      refine Fin.lastCases ?_ (fun i => ?_) t
      · have hpref : batchTablePrefix
            (S.next b hnlt).baseReply (Fin.last n) = S.baseReply := by
          funext j
          let k : Fin n := ⟨j.1, by omega⟩
          change Fin.lastCases b S.baseReply ⟨j.1, by omega⟩ =
            S.baseReply k
          have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) =
              Fin.castSucc k := Fin.ext rfl
          rw [hj, Fin.lastCases_castSucc]
        have hreconstruct :
            uniformBatchStateFromHistory d T A n (Nat.le_of_lt hnlt)
                S.baseReply = S := by
          rw [hbase]
        simp only [uniformBatchStateFromHistory, UniformBatchState.next,
          Fin.lastCases_last, Fin.val_last]
        change S.frame.project (A.nextQuery n S.reply) =
          (uniformZeroRespectingComponent d T A).nextQuery n
            (batchTablePrefix (S.next b hnlt).baseReply (Fin.last n))
        rw [hpref]
        simp only [uniformZeroRespectingComponent, hnlt, ↓reduceDIte]
        rw [hreconstruct]
      · have hpref : batchTablePrefix
            (S.next b hnlt).baseReply (Fin.castSucc i) =
            batchTablePrefix S.baseReply i := by
          funext j
          let k : Fin n := ⟨j.1, by omega⟩
          change Fin.lastCases b S.baseReply ⟨j.1, by omega⟩ =
            S.baseReply k
          have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) =
              Fin.castSucc k := Fin.ext rfl
          rw [hj, Fin.lastCases_castSucc]
        simp only [uniformBatchStateFromHistory, UniformBatchState.next,
          Fin.lastCases_castSucc, Fin.val_castSucc]
        change S.baseQuery i =
          (uniformZeroRespectingComponent d T A).nextQuery i.1
            (batchTablePrefix (S.next b hnlt).baseReply (Fin.castSucc i))
        rw [hpref]
        exact ih (by omega) histPrefix i

/-- Complete every still-hidden base column after the `T` online rounds.
The completion may depend on the realized transcript, as the matrix `U` is
existentially quantified after the base problem in the manuscript. -/
structure UniformCompletedBatchTable (d T : Nat)
    (A : DeterministicFullOracleComponent (d + T)) where
  adaptive : UniformBatchState d T T A
  finalFrame : PublishedFrame d T
  frame_complete : finalFrame.published = Finset.univ
  final_project : ∀ s,
    adaptive.baseQuery s = finalFrame.project (adaptive.query s)
  final_reply_rotated : ∀ s,
    adaptive.reply s = rotateBaseReply finalFrame (adaptive.baseReply s)

theorem UniformBatchState.exists_completion {d T : Nat}
    {A : DeterministicFullOracleComponent (d + T)}
    (S : UniformBatchState d T T A) :
    ∃ C : UniformCompletedBatchTable d T A, C.adaptive = S := by
  classical
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
    final_reply_rotated := ?_ }, rfl⟩
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

theorem UniformCompletedBatchTable.frame_orthonormal {d T : Nat}
    {A : DeterministicFullOracleComponent (d + T)}
    (C : UniformCompletedBatchTable d T A) :
    WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame C.finalFrame.column := by
  intro i j
  apply C.finalFrame.orthonormal_on i
  · rw [C.frame_complete]
    exact Finset.mem_univ i
  · rw [C.frame_complete]
    exact Finset.mem_univ j

/-- Repackage a uniform table as the earlier oracle-indexed table once an
actual base oracle has been shown to produce its stored base replies. -/
def UniformCompletedBatchTable.toCompletedDynamicBatchTable
    {d T : Nat} {A : DeterministicFullOracleComponent (d + T)}
    (C : UniformCompletedBatchTable d T A)
    (baseOracle : EVector d → FullOracleReply d)
    (hbase : ∀ s,
      C.adaptive.baseReply s = baseOracle (C.adaptive.baseQuery s)) :
    CompletedDynamicBatchTable d T A baseOracle where
  adaptive := {
    frame := C.adaptive.frame
    query := C.adaptive.query
    baseQuery := C.adaptive.baseQuery
    baseReply := C.adaptive.baseReply
    reply := C.adaptive.reply
    causal := C.adaptive.causal
    baseQuery_eq_project := C.adaptive.baseQuery_eq_project
    baseReply_eq := hbase
    reply_eq_rotated := C.adaptive.reply_eq_rotated
    support_published := C.adaptive.support_published
    published_has_origin := C.adaptive.published_has_origin
    base_zero_respecting := C.adaptive.base_zero_respecting }
  finalFrame := C.finalFrame
  frame_complete := C.frame_complete
  final_project := C.final_project
  final_reply_rotated := C.final_reply_rotated

/-- On an actual base problem, the reconstructed table's base queries are
exactly the actual queries of the single uniform low-dimensional component.
-/
theorem uniformBatchState_actual_base_queries
    {d T : Nat} (A : DeterministicFullOracleComponent (d + T))
    (P : FullOracleProblem d) :
    let Z := uniformZeroRespectingComponent d T A
    let history := Z.queriedTranscript P T
    let S := uniformBatchStateFromHistory d T A T le_rfl history
    ∀ t : Fin T, Z.queriedAt P t.1 = S.baseQuery t := by
  dsimp only
  let Z := uniformZeroRespectingComponent d T A
  let history := Z.queriedTranscript P T
  let S := uniformBatchStateFromHistory d T A T le_rfl history
  have hreply : S.baseReply = history :=
    uniformBatchStateFromHistory_baseReply d T A T le_rfl history
  have hcausal : BatchIsCausalTable Z S.baseQuery S.baseReply :=
    uniformBatchStateFromHistory_base_causal d T A T le_rfl history
  intro t
  rw [DeterministicFullOracleComponent.queriedAt_eq_nextQuery]
  rw [hcausal t]
  congr 1
  funext i
  let k : Fin T := ⟨i.1, by omega⟩
  change fullOracle P (Z.queriedAt P i.1) = S.baseReply k
  rw [hreply]
  rfl

theorem uniformZeroRespectingComponent_queriedAt_of_ge
    {d T : Nat} (A : DeterministicFullOracleComponent (d + T))
    (P : FullOracleProblem d) {t : Nat} (ht : T ≤ t) :
    (uniformZeroRespectingComponent d T A).queriedAt P t = 0 := by
  rw [DeterministicFullOracleComponent.queriedAt_eq_nextQuery]
  simp [uniformZeroRespectingComponent, Nat.not_lt_of_ge ht]

/-- The function-independent state can be specialized to any actual base
problem after the uniform component has been fixed. -/
theorem exists_completedDynamicBatchTable_for_uniformComponent
    {d T : Nat} (A : DeterministicFullOracleComponent (d + T))
    (P : FullOracleProblem d) :
    let Z := uniformZeroRespectingComponent d T A
    ∃ C : CompletedDynamicBatchTable d T A (fullOracle P),
      ∀ t : Fin T, Z.queriedAt P t.1 = C.adaptive.baseQuery t := by
  dsimp only
  let Z := uniformZeroRespectingComponent d T A
  let history := Z.queriedTranscript P T
  let S := uniformBatchStateFromHistory d T A T le_rfl history
  obtain ⟨CU, hCU⟩ := S.exists_completion
  have hreply : S.baseReply = history :=
    uniformBatchStateFromHistory_baseReply d T A T le_rfl history
  have hquery : ∀ t : Fin T, Z.queriedAt P t.1 = S.baseQuery t :=
    uniformBatchState_actual_base_queries A P
  have hbase : ∀ s, S.baseReply s = fullOracle P (S.baseQuery s) := by
    intro s
    rw [hreply]
    change fullOracle P (Z.queriedAt P s.1) = fullOracle P (S.baseQuery s)
    rw [hquery s]
  have hbaseCU : ∀ s,
      CU.adaptive.baseReply s = fullOracle P (CU.adaptive.baseQuery s) := by
    simpa [hCU] using hbase
  let C := CU.toCompletedDynamicBatchTable (fullOracle P) hbaseCU
  refine ⟨C, ?_⟩
  intro t
  change Z.queriedAt P t.1 = CU.adaptive.baseQuery t
  rw [hCU]
  exact hquery t

/-- A flattened full-oracle problem for a literal block objective. -/
def flattenedFullOracleProblem {M N : Nat} (rho : ℝ)
    (f : BlockVec M N → ℝ) (baseStationarity : BlockVec M N → ℝ) :
    FullOracleProblem (M * N) where
  objective := fun x => f (unflatten x)
  subdiff := fun x => flatten '' fullSubdiff rho f (unflatten x)
  stationarity := fun x => baseStationarity (unflatten x)

@[simp] theorem fullOracle_flattenedFullOracleProblem {M N : Nat}
    (rho : ℝ) (f : BlockVec M N → ℝ)
    (baseStationarity : BlockVec M N → ℝ) (x : EVector (M * N)) :
    fullOracle (flattenedFullOracleProblem rho f baseStationarity) x =
      flattenedFullOracleReply rho f x := rfl

/-- Block-valued actual query sequence of the single uniform component on a
literal flattened base problem. -/
def uniformBlockQuery {M N T : Nat}
    (A : DeterministicFullOracleComponent (M * N + T))
    (rho : ℝ) (f : BlockVec M N → ℝ)
    (baseStationarity : BlockVec M N → ℝ) (t : Nat) : BlockVec M N :=
  unflatten
    ((uniformZeroRespectingComponent (M * N) T A).queriedAt
      (flattenedFullOracleProblem rho f baseStationarity) t)

/-- Literal finite-horizon resisting-oracle lemma with the manuscript's
uniform quantifier order:

`∀ T A_det, ∃ one causal A_zr, ∀ rho f, ∃ U`.

The component `Z` is fixed before `rho`, `f`, and the stationarity field.  On
every literal full-subdifferential transcript its actual block queries are
generalized full-set zero-respecting, and through the finite horizon they
are exactly the projections of the ambient algorithm's queries on the
rotated problem. -/
theorem finiteHorizon_uniform_resisting_oracle
    (M N T : Nat)
    (A : DeterministicFullOracleComponent (M * N + T)) :
    ∃ Z : DeterministicFullOracleComponent (M * N),
      Z = uniformZeroRespectingComponent (M * N) T A ∧
      ∀ (rho : ℝ), 0 ≤ rho →
      ∀ (f : BlockVec M N → ℝ)
        (baseStationarity : BlockVec M N → ℝ),
        ∃ U : Fin (M * N) → EVector (M * N + T),
          WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U ∧
          FullSetZeroRespecting (fullSubdiff rho f)
            (fun t => unflatten
              (Z.queriedAt
                (flattenedFullOracleProblem rho f baseStationarity) t)) ∧
          ∀ t : Fin T,
            unflatten
                (Z.queriedAt
                  (flattenedFullOracleProblem rho f baseStationarity) t.1) =
              blockProject U
                (A.queriedAt
                  (rotatedFullOracleProblem rho f U baseStationarity) t.1) := by
  let Z := uniformZeroRespectingComponent (M * N) T A
  refine ⟨Z, rfl, ?_⟩
  intro rho hrho f baseStationarity
  let Pbase := flattenedFullOracleProblem rho f baseStationarity
  obtain ⟨C, hZquery⟩ :=
    exists_completedDynamicBatchTable_for_uniformComponent A Pbase
  have hframe : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame C.finalFrame.column :=
    C.frame_orthonormal
  let Pambient : FullOracleProblem (M * N + T) :=
    rotatedFullOracleProblem rho f C.finalFrame.column baseStationarity
  have hbaseFullSet : ∀ z,
      ((fullOracle Pbase) (flatten z)).subdiff =
        flatten '' fullSubdiff rho f z := by
    intro z
    change flatten '' fullSubdiff rho f (unflatten (flatten z)) =
      flatten '' fullSubdiff rho f z
    rw [unflatten_flatten]
  have hrotated : ∀ t,
      fullOracle Pambient (C.adaptive.query t) =
        rotateBaseReply C.finalFrame
          ((fullOracle Pbase)
            (C.finalFrame.project (C.adaptive.query t))) := by
    intro t
    simpa [Pambient, Pbase] using
      (fullOracle_rotated_eq_rotateBaseReply rho hrho f C.finalFrame
        hframe baseStationarity (C.adaptive.query t))
  obtain ⟨_htranscript, _hambientQuery, hzero, hproject⟩ :=
    C.actual_transcript_and_fullSetZeroRespecting
      (fullSubdiff rho f) Pambient hbaseFullSet hrotated
  have hblock : ∀ t : Nat,
      C.blockQuery t = unflatten (Z.queriedAt Pbase t) := by
    intro t
    unfold CompletedDynamicBatchTable.blockQuery
    split
    next ht =>
      rw [hZquery ⟨t, ht⟩]
    next ht =>
      have hge : T ≤ t := Nat.le_of_not_gt ht
      rw [uniformZeroRespectingComponent_queriedAt_of_ge A Pbase hge]
      exact unflatten_zero.symm
  have hzeroActual : FullSetZeroRespecting (fullSubdiff rho f)
      (fun t => unflatten (Z.queriedAt Pbase t)) := by
    have hfun : (fun t => unflatten (Z.queriedAt Pbase t)) = C.blockQuery := by
      funext t
      exact (hblock t).symm
    rw [hfun]
    exact hzero
  refine ⟨C.finalFrame.column, hframe, ?_, ?_⟩
  · simpa [Pbase] using hzeroActual
  · intro t
    have hp := hproject t
    rw [hblock t.1] at hp
    simpa [Pbase, Pambient, blockProject] using hp

end

end WeaklyConvexLowerBound

