import WeaklyConvexLowerBound.FullOracleModel
import WeaklyConvexLowerBound.Foundation.HiddenDirections

/-!
# A finite-horizon resisting frame for a full set-valued oracle

This file isolates the information-theoretic part of the resisting-oracle
argument.  Replies may contain the entire subdifferential set.  The only
assumption made about such a reply is that, at round `t`, it is produced from
the `t+1` directions which have already been published and from the query's
coordinates in those directions.

The construction is deliberately independent of the eventual hard
function.  A later module only has to prove that its rotated full oracle
agrees with `PublishedReplyRule` on the finitely many constructed queries.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

abbrev PublishedReplyRule (D : Nat) :=
  (t : Nat) →
    (Fin (t + 1) → EVector D) →
    (Fin (t + 1) → ℝ) →
    FullOracleReply D

/-- The part of a length-`K` frame which has been published by round `t`.
The direction bearing index `t` is included because it is selected after
seeing query `t` and before returning reply `t`. -/
def revealedPrefix {D K : Nat} (U : Fin K → EVector D) (t : Fin K) :
    Fin (t.1 + 1) → EVector D :=
  fun i => U ⟨i.1, by omega⟩

/-- The finite reply history before a table entry `t`. -/
def tablePrefix {D K : Nat} (reply : Fin K → FullOracleReply D)
    (t : Fin K) : FullReplyHistory D t.1 :=
  fun i => reply ⟨i.1, by omega⟩

/-- Causality expressed without any untyped infinite transcript: the `t`-th
query is the algorithm applied to exactly the first `t` table replies. -/
def IsCausalTable {D K : Nat} (A : DeterministicFullOracleComponent D)
    (query : Fin K → EVector D) (reply : Fin K → FullOracleReply D) : Prop :=
  ∀ t, query t = A.nextQuery t.1 (tablePrefix reply t)

/-- Every query has zero projection onto its as-yet hidden directions.  At
round `t`, directions with indices `< t` may already occur in the transcript,
while directions with indices `≥ t` have not been available when the query
was chosen. -/
def FrameZeroRespecting {D K : Nat} (U : Fin K → EVector D)
    (query : Fin K → EVector D) : Prop :=
  ∀ t s, t.1 ≤ s.1 →
    WeaklyConvexLowerBound.Foundation.frameProject U (query t) s = 0

/-- A complete finite table produced by the abstract resisting construction. -/
structure FullSetResistingTable {D K : Nat}
    (A : DeterministicFullOracleComponent D)
    (R : PublishedReplyRule D) where
  direction : Fin K → EVector D
  query : Fin K → EVector D
  reply : Fin K → FullOracleReply D
  frame_orthonormal : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame direction
  causal : IsCausalTable A query reply
  zero_respecting : FrameZeroRespecting direction query
  published_reply : ∀ t,
    reply t = R t.1 (revealedPrefix direction t)
      (WeaklyConvexLowerBound.Foundation.frameProject (revealedPrefix direction t) (query t))

/-- A sufficiently large Euclidean space contains a unit vector orthogonal
simultaneously to the current orthonormal frame and to all queries seen so
far (in particular, to the current query). -/
theorem exists_unit_orthogonal_to_basis_and_queries {D K : Nat}
    (U : Fin K → EVector D) (query : Fin (K + 1) → EVector D)
    (hcapacity : K + (K + 1) < D) :
    ∃ u : EVector D,
      WeaklyConvexLowerBound.Foundation.evecDotValue u u = 1 ∧
      (∀ i, WeaklyConvexLowerBound.Foundation.evecDotValue (U i) u = 0) ∧
      ∀ t, WeaklyConvexLowerBound.Foundation.evecDotValue (query t) u = 0 := by
  let constraints : List (EVector D) := List.ofFn U ++ List.ofFn query
  have hlength : constraints.length < D := by
    simpa [constraints] using hcapacity
  obtain ⟨u, hu, horth⟩ :=
    WeaklyConvexLowerBound.Foundation.exists_unit_orthogonal_to_list constraints hlength
  refine ⟨u, hu, ?_, ?_⟩
  · intro i
    exact horth (U i) (by
      apply List.mem_append_left
      exact List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro t
    exact horth (query t) (by
      apply List.mem_append_right
      exact List.mem_ofFn.mpr ⟨t, rfl⟩)

/-- Appending a unit direction orthogonal to an orthonormal frame preserves
orthonormality. -/
theorem isOrthonormalFrame_lastCases {D K : Nat}
    {U : Fin K → EVector D} {u : EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (hu : WeaklyConvexLowerBound.Foundation.evecDotValue u u = 1)
    (horth : ∀ i, WeaklyConvexLowerBound.Foundation.evecDotValue (U i) u = 0) :
    WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame (Fin.lastCases u U) := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun b => ?_) j
    · simpa using hu
    · have hne : Fin.last K ≠ Fin.castSucc b := by
        intro h
        have := congrArg Fin.val h
        have hb := b.isLt
        simp only [Fin.val_last, Fin.val_castSucc] at this
        omega
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, if_neg hne]
      rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm]
      exact horth b
  · intro j
    refine Fin.lastCases ?_ (fun b => ?_) j
    · have hne : Fin.castSucc a ≠ Fin.last K := by
        intro h
        have := congrArg Fin.val h
        have ha := a.isLt
        simp only [Fin.val_castSucc, Fin.val_last] at this
        omega
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, if_neg hne]
      exact horth a
    · simp only [Fin.lastCases_castSucc]
      simpa using hU a b

/-- Exact table replies force the causal table to be the actual recursively
generated query sequence.  This is the key bridge from a resisting transcript
to `DeterministicFullOracleComponent.queriedAt`. -/
theorem IsCausalTable.eq_actual_queries {D K : Nat}
    {A : DeterministicFullOracleComponent D}
    {P : FullOracleProblem D}
    {query : Fin K → EVector D} {reply : Fin K → FullOracleReply D}
    (hcausal : IsCausalTable A query reply)
    (hexact : ∀ t, reply t = fullOracle P (query t)) :
    ∀ t : Fin K,
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
          DeterministicFullOracleComponent.replyAt tablePrefix
        let k : Fin K := ⟨i.1, by omega⟩
        have hi := ih i.1 i.2 (by omega)
        change fullOracle P
            (DeterministicFullOracleComponent.queriedAt A P i.1) = reply k
        rw [hi]
        exact (hexact k).symm
  intro t
  exact hmain t.1 t.2

private theorem extend_causal_table {D K : Nat}
    {A : DeterministicFullOracleComponent D}
    {query : Fin K → EVector D} {reply : Fin K → FullOracleReply D}
    (hcausal : IsCausalTable A query reply)
    (x : EVector D) (hx : x = A.nextQuery K reply)
    (r : FullOracleReply D) :
    IsCausalTable A (Fin.lastCases x query) (Fin.lastCases r reply) := by
  intro t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · simp only [Fin.lastCases_last, Fin.val_last]
    change x = A.nextQuery K
      (tablePrefix (Fin.lastCases r reply) (Fin.last K))
    rw [hx]
    congr 1
    funext j
    change reply j = Fin.lastCases r reply ⟨j.1, by omega⟩
    have hj : (⟨j.1, by omega⟩ : Fin (K + 1)) = Fin.castSucc j :=
      Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]
  · simp only [Fin.lastCases_castSucc, Fin.val_castSucc]
    change query i = A.nextQuery i.1
      (tablePrefix (Fin.lastCases r reply) (Fin.castSucc i))
    rw [hcausal i]
    congr 1
    funext j
    let k : Fin K := ⟨j.1, by omega⟩
    change reply k = Fin.lastCases r reply ⟨j.1, by omega⟩
    have hj : (⟨j.1, by omega⟩ : Fin (K + 1)) = Fin.castSucc k :=
      Fin.ext rfl
    rw [hj, Fin.lastCases_castSucc]

private theorem extend_zero_respecting {D K : Nat}
    {U : Fin K → EVector D} {query : Fin K → EVector D}
    (hzero : FrameZeroRespecting U query)
    (x u : EVector D)
    (hqueryOrth : ∀ t : Fin (K + 1),
      WeaklyConvexLowerBound.Foundation.evecDotValue (Fin.lastCases x query t) u = 0) :
    FrameZeroRespecting (Fin.lastCases u U) (Fin.lastCases x query) := by
  intro t
  refine Fin.lastCases ?_ (fun a => ?_) t
  · intro s hle
    have hs : s = Fin.last K := by
      apply Fin.ext
      simp only [Fin.val_last] at hle ⊢
      have hslt := s.isLt
      omega
    subst s
    unfold WeaklyConvexLowerBound.Foundation.frameProject
    simp only [Fin.lastCases_last]
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm]
    simpa using hqueryOrth (Fin.last K)
  · intro s
    refine Fin.lastCases ?_ (fun b => ?_) s
    · intro _
      unfold WeaklyConvexLowerBound.Foundation.frameProject
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm]
      simpa using hqueryOrth (Fin.castSucc a)
    · intro hab
      unfold WeaklyConvexLowerBound.Foundation.frameProject
      simp only [Fin.lastCases_castSucc]
      simpa [FrameZeroRespecting, WeaklyConvexLowerBound.Foundation.frameProject] using
        hzero a b hab

/-- Finite-horizon resisting-frame recursion.  At round `t`, causality first
fixes the query from the old replies.  A new unit direction is then selected
orthogonal to every old frame vector and every query through round `t`.
Finally the rule returns a reply using only the published frame and the
published coordinates of that query.

The explicit bound `2*K < D` is conservative but convenient: before the last
of `K` rounds there are `K-1` frame constraints and `K` query constraints. -/
theorem exists_fullSetResistingTable {D K : Nat}
    (A : DeterministicFullOracleComponent D)
    (R : PublishedReplyRule D)
    (hcapacity : 2 * K < D) :
    Nonempty (FullSetResistingTable (K := K) A R) := by
  have build : ∀ n : Nat, 2 * n < D →
      Nonempty (FullSetResistingTable (K := n) A R) := by
    intro n
    induction n with
    | zero =>
        intro _
        let S : FullSetResistingTable (K := 0) A R := {
          direction := Fin.elim0
          query := Fin.elim0
          reply := Fin.elim0
          frame_orthonormal := by intro i; exact Fin.elim0 i
          causal := by intro i; exact Fin.elim0 i
          zero_respecting := by intro i; exact Fin.elim0 i
          published_reply := by intro i; exact Fin.elim0 i
        }
        exact ⟨S⟩
    | succ n ih =>
        intro hn
        have hnold : 2 * n < D := by omega
        let S := Classical.choice (ih hnold)
        let x : EVector D := A.nextQuery n S.reply
        let qnext : Fin (n + 1) → EVector D := Fin.lastCases x S.query
        have hchoose : n + (n + 1) < D := by omega
        obtain ⟨u, hu, hUu, hqu⟩ :=
          exists_unit_orthogonal_to_basis_and_queries S.direction qnext hchoose
        let Unext : Fin (n + 1) → EVector D := Fin.lastCases u S.direction
        let r : FullOracleReply D :=
          R n Unext (WeaklyConvexLowerBound.Foundation.frameProject Unext x)
        let rnext : Fin (n + 1) → FullOracleReply D := Fin.lastCases r S.reply
        let Snext : FullSetResistingTable (K := n + 1) A R := {
          direction := Unext
          query := qnext
          reply := rnext
          frame_orthonormal := by
            exact isOrthonormalFrame_lastCases S.frame_orthonormal hu hUu
          causal := by
            apply extend_causal_table S.causal x rfl r
          zero_respecting := by
            apply extend_zero_respecting S.zero_respecting x u
            exact hqu
          published_reply := by
            intro t
            refine Fin.lastCases ?_ (fun i => ?_) t
            · simp only [rnext, qnext, Fin.lastCases_last, Fin.val_last]
              have hp : revealedPrefix Unext (Fin.last n) = Unext := by
                funext i
                rfl
              simp [r, hp]
            · simp only [rnext, qnext, Fin.lastCases_castSucc,
                Fin.val_castSucc]
              have hp : revealedPrefix Unext (Fin.castSucc i) =
                  revealedPrefix S.direction i := by
                funext j
                have hi := i.isLt
                have hjlt := j.isLt
                change j.1 < i.1 + 1 at hjlt
                have hjle : j.1 ≤ i.1 := by omega
                have hjn : j.1 < n := lt_of_le_of_lt hjle hi
                unfold revealedPrefix Unext
                change Fin.lastCases u S.direction ⟨j.1, by omega⟩ =
                  S.direction ⟨j.1, hjn⟩
                have hj : (⟨j.1, by omega⟩ : Fin (n + 1)) =
                    Fin.castSucc (⟨j.1, hjn⟩ : Fin n) := Fin.ext rfl
                rw [hj, Fin.lastCases_castSucc]
              rw [S.published_reply i, hp]
        }
        exact ⟨Snext⟩
  exact build K hcapacity

/-- If a concrete problem's full oracle agrees with the published-coordinate
rule on the constructed finite table, then that table is not merely
synthetic: it is the algorithm's actual transcript.  Consequently every
actual query through the horizon is zero in all not-yet-published frame
coordinates. -/
theorem FullSetResistingTable.actual_transcript_and_zero_respecting
    {D K : Nat} {A : DeterministicFullOracleComponent D}
    {R : PublishedReplyRule D}
    (S : FullSetResistingTable (K := K) A R)
    (P : FullOracleProblem D)
    (horacle : ∀ t,
      fullOracle P (S.query t) =
        R t.1 (revealedPrefix S.direction t)
          (WeaklyConvexLowerBound.Foundation.frameProject
            (revealedPrefix S.direction t) (S.query t))) :
    DeterministicFullOracleComponent.queriedTranscript A P K = S.reply ∧
      ∀ t s : Fin K, t.1 ≤ s.1 →
        WeaklyConvexLowerBound.Foundation.frameProject S.direction
          (DeterministicFullOracleComponent.queriedAt A P t.1) s = 0 := by
  have hexact : ∀ t, S.reply t = fullOracle P (S.query t) := by
    intro t
    rw [S.published_reply t, horacle t]
  have hquery := S.causal.eq_actual_queries hexact
  constructor
  · funext t
    unfold DeterministicFullOracleComponent.queriedTranscript
      DeterministicFullOracleComponent.replyAt
    rw [hquery t, ← hexact t]
  · intro t s hts
    rw [hquery t]
    exact S.zero_respecting t s hts

end

end WeaklyConvexLowerBound


