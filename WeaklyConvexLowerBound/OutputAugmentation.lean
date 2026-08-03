import WeaklyConvexLowerBound.FullOracleModel

/-!
# Turning a deterministic output into one additional full-oracle query

The paper allows a deterministic method to return an arbitrary function of
its transcript, rather than requiring the returned point to be one of the
queried points.  This file verifies the standard reduction: at any positive
time `T`, replace query `T` by the original method's output after the first
`T` replies.  The first `T` queries (and hence their replies) are unchanged.
-/

namespace WeaklyConvexLowerBound

noncomputable section

namespace DeterministicFullOracleComponent

/-- A component whose query at the single time `T` is the original
component's output from the preceding transcript.  Positivity of `T` ensures
that the required initial query remains zero. -/
def withOutputAsQuery {d : Nat} (A : DeterministicFullOracleComponent d)
    (T : Nat) (hT : 0 < T) : DeterministicFullOracleComponent d where
  nextQuery := fun t history =>
    if h : t = T then A.output T (h ▸ history) else A.nextQuery t history
  initial_query := by
    simp [Nat.ne_of_lt hT, A.initial_query]
  output := A.output

/-- A zero-reply output cannot replace the mandatory initial query, which is
fixed to zero by the oracle model.  It can instead be used as query `1`,
after that mandatory query and its (unused) reply. -/
def withInitialOutputAsSecondQuery {d : Nat}
    (A : DeterministicFullOracleComponent d) :
    DeterministicFullOracleComponent d where
  nextQuery := fun t _history =>
    if t = 0 then 0 else if t = 1 then A.output 0 (emptyFullHistory d) else 0
  initial_query := by simp
  output := A.output

/-- Before the augmented query, the new and original actual query sequences
coincide exactly. -/
theorem queriedAt_withOutputAsQuery_of_lt {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (T : Nat) (hT : 0 < T) {t : Nat} (ht : t < T) :
    queriedAt (A.withOutputAsQuery T hT) P t = queriedAt A P t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [queriedAt_eq_nextQuery, queriedAt_eq_nextQuery]
      simp only [withOutputAsQuery, dif_neg (Nat.ne_of_lt ht)]
      apply congrArg (A.nextQuery t)
      funext i
      simp only [queriedTranscript, replyAt]
      exact congrArg (fullOracle P)
        (ih i i.isLt (lt_trans i.isLt ht))

/-- Query `T` of the augmented component is literally the original output
after `T` replies. -/
theorem queriedAt_withOutputAsQuery_at {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (T : Nat) (hT : 0 < T) :
    queriedAt (A.withOutputAsQuery T hT) P T = outputAt A P T := by
  rw [queriedAt_eq_nextQuery]
  simp only [withOutputAsQuery]
  unfold outputAt
  apply congrArg (A.output T)
  funext i
  simp only [queriedTranscript, replyAt]
  exact congrArg (fullOracle P)
    (queriedAt_withOutputAsQuery_of_lt A P T hT i.isLt)

/-- Query `1` of the special zero-reply augmentation is the original output
formed from the empty transcript. -/
theorem queriedAt_withInitialOutputAsSecondQuery_one {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d) :
    queriedAt A.withInitialOutputAsSecondQuery P 1 = outputAt A P 0 := by
  rw [queriedAt_eq_nextQuery]
  simp only [withInitialOutputAsSecondQuery, one_ne_zero, ↓reduceIte]
  unfold outputAt
  apply congrArg (A.output 0)
  funext i
  exact Fin.elim0 i

/-- Failure of the augmented method through its extra query implies failure
of the original method's arbitrary transcript-dependent output. -/
theorem outputAt_fails_of_augmented_failsWithin {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (epsilon : Real) (T : Nat) (hT : 0 < T)
    (hfail : FailsWithin (A.withOutputAsQuery T hT) P epsilon (T + 1)) :
    ¬ P.stationarity (outputAt A P T) ≤ epsilon := by
  intro hout
  apply hfail T (by omega)
  unfold HitsAt
  rw [queriedAt_withOutputAsQuery_at A P T hT]
  exact hout

end DeterministicFullOracleComponent

namespace DimensionWiseFullOracleAlgorithm

/-- Apply output-as-query augmentation uniformly in every dimension. -/
def withOutputAsQuery (A : DimensionWiseFullOracleAlgorithm)
    (T : Nat) (hT : 0 < T) : DimensionWiseFullOracleAlgorithm where
  component := fun d => (A.component d).withOutputAsQuery T hT

/-- Uniform dimension-wise zero-reply output augmentation. -/
def withInitialOutputAsSecondQuery (A : DimensionWiseFullOracleAlgorithm) :
    DimensionWiseFullOracleAlgorithm where
  component := fun d => (A.component d).withInitialOutputAsSecondQuery

end DimensionWiseFullOracleAlgorithm

/-- A query lower bound through time `T` automatically covers an arbitrary
deterministic output formed from the first `T` replies. -/
theorem outputAt_failure_of_fullOracleComplexityAtLeast
    {C : DimensionedProblemClass} {epsilon : Real} {T : Nat}
    (hT : 0 < T)
    (hlower : FullOracleComplexityAtLeast C epsilon (T + 1)) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, C d P ∧
        ¬ P.stationarity ((A.component d).outputAt P T) ≤ epsilon := by
  intro A
  obtain ⟨d, P, hmem, hfail⟩ :=
    hlower (A.withOutputAsQuery T hT)
  exact ⟨d, P, hmem,
    DeterministicFullOracleComponent.outputAt_fails_of_augmented_failsWithin
      (A.component d) P epsilon T hT hfail⟩

/-- The lower bound also covers an arbitrary fixed output returned before
any oracle reply: use it as query `1` after the mandatory zero query. -/
theorem outputAt_zero_failure_of_fullOracleComplexityAtLeast_two
    {C : DimensionedProblemClass} {epsilon : Real}
    (hlower : FullOracleComplexityAtLeast C epsilon 2) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, C d P ∧
        ¬ P.stationarity ((A.component d).outputAt P 0) ≤ epsilon := by
  intro A
  obtain ⟨d, P, hmem, hfail⟩ :=
    hlower A.withInitialOutputAsSecondQuery
  refine ⟨d, P, hmem, ?_⟩
  intro hout
  apply hfail 1 (by omega)
  unfold DeterministicFullOracleComponent.HitsAt
  change P.stationarity
    (DeterministicFullOracleComponent.queriedAt
      (A.component d).withInitialOutputAsSecondQuery P 1) ≤ epsilon
  rw [DeterministicFullOracleComponent.queriedAt_withInitialOutputAsSecondQuery_one]
  exact hout

end

end WeaklyConvexLowerBound

