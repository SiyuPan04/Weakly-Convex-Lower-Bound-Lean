import WeaklyConvexLowerBound.Basic

/-!
# Dimension-correct deterministic full-set oracle model

The manuscript takes a union over Euclidean dimensions.  This file makes the
dimension index explicit: a deterministic algorithm is a family with one
causal component for every dimension, and each component can inspect only its
finite history of value/full-subdifferential replies.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- A Euclidean coordinate vector in a fixed dimension. -/
abbrev EVector (d : Nat) := Fin d → ℝ

/-- The full reply returned at one query. -/
structure FullOracleReply (d : Nat) where
  value : ℝ
  subdiff : Set (EVector d)

/-- A fixed-dimensional problem together with the exact set-valued oracle and
the stationarity quantity used by the hitting test.  Later files instantiate
`subdiff` with the quadratic-support subdifferential of the objective. -/
structure FullOracleProblem (d : Nat) where
  objective : EVector d → ℝ
  subdiff : EVector d → Set (EVector d)
  stationarity : EVector d → ℝ

def fullOracle {d : Nat} (P : FullOracleProblem d) (x : EVector d) :
    FullOracleReply d where
  value := P.objective x
  subdiff := P.subdiff x

/-- Exactly the replies available immediately before query `t`. -/
abbrev FullReplyHistory (d t : Nat) := Fin t → FullOracleReply d

def emptyFullHistory (d : Nat) : FullReplyHistory d 0 := Fin.elim0

/-- A causal deterministic component in one fixed dimension. -/
structure DeterministicFullOracleComponent (d : Nat) where
  nextQuery : (t : Nat) → FullReplyHistory d t → EVector d
  initial_query : nextQuery 0 (emptyFullHistory d) = 0
  output : (t : Nat) → FullReplyHistory d t → EVector d

namespace DeterministicFullOracleComponent

/-- The actual query recursion.  Every recursive call is indexed by `Fin t`,
so causality is enforced by the type. -/
def queriedAt {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (t : Nat) : EVector d :=
  A.nextQuery t fun i => fullOracle P (queriedAt A P i)
termination_by t
decreasing_by exact i.isLt

def replyAt {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (t : Nat) : FullOracleReply d :=
  fullOracle P (queriedAt A P t)

def queriedTranscript {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (t : Nat) : FullReplyHistory d t :=
  fun i => replyAt A P i

theorem queriedAt_eq_nextQuery {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (t : Nat) :
    queriedAt A P t = A.nextQuery t (queriedTranscript A P t) := by
  rw [queriedAt]
  rfl

@[simp] theorem queriedAt_zero {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d) :
    queriedAt A P 0 = 0 := by
  rw [queriedAt]
  convert A.initial_query

def outputAt {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (t : Nat) : EVector d :=
  A.output t (queriedTranscript A P t)

def HitsAt {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (ε : ℝ) (t : Nat) : Prop :=
  P.stationarity (queriedAt A P t) ≤ ε

def HitsWithin {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (ε : ℝ) (T : Nat) : Prop :=
  ∃ t < T, HitsAt A P ε t

def FailsWithin {d : Nat} (A : DeterministicFullOracleComponent d)
    (P : FullOracleProblem d) (ε : ℝ) (T : Nat) : Prop :=
  ∀ t < T, ¬ HitsAt A P ε t

theorem failsWithin_iff_not_hitsWithin {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (ε : ℝ) (T : Nat) :
    FailsWithin A P ε T ↔ ¬ HitsWithin A P ε T := by
  constructor
  · intro hfail ⟨t, ht, hhit⟩
    exact hfail t ht hhit
  · intro hnot t ht hhit
    exact hnot ⟨t, ht, hhit⟩

/-- Failure through query index `H` is failure within the strict horizon
`H+1`; this is the type-correct off-by-one convention used by the Lean proof. -/
theorem failsWithin_succ_of_failure_through {d : Nat}
    (A : DeterministicFullOracleComponent d) (P : FullOracleProblem d)
    (ε : ℝ) (H : Nat)
    (hfail : ∀ t ≤ H, ¬ HitsAt A P ε t) :
    FailsWithin A P ε (H + 1) := by
  intro t ht
  exact hfail t (by omega)

end DeterministicFullOracleComponent

/-- One objective-independent component for every dimension. -/
structure DimensionWiseFullOracleAlgorithm where
  component : (d : Nat) → DeterministicFullOracleComponent d

/-- A dimension-indexed function class avoids forming an ill-typed literal
union of function spaces with different domains. -/
abbrev DimensionedProblemClass :=
  (d : Nat) → FullOracleProblem d → Prop

def FullOracleSolvesWithin (A : DimensionWiseFullOracleAlgorithm)
    (C : DimensionedProblemClass) (ε : ℝ) (T : Nat) : Prop :=
  ∀ d P, C d P →
    DeterministicFullOracleComponent.HitsWithin (A.component d) P ε T

/-- Threshold formulation of the deterministic lower complexity bound. -/
def FullOracleComplexityAtLeast (C : DimensionedProblemClass)
    (ε : ℝ) (K : Nat) : Prop :=
  ∀ A : DimensionWiseFullOracleAlgorithm,
    ∃ d P, C d P ∧
      DeterministicFullOracleComponent.FailsWithin (A.component d) P ε K

theorem fullOracleComplexityAtLeast_iff
    {C : DimensionedProblemClass} {ε : ℝ} {K : Nat} :
    FullOracleComplexityAtLeast C ε K ↔
      ∀ A : DimensionWiseFullOracleAlgorithm,
        ¬ FullOracleSolvesWithin A C ε K := by
  constructor
  · intro hlower A hsolve
    obtain ⟨d, P, hmem, hfail⟩ := hlower A
    exact (DeterministicFullOracleComponent.failsWithin_iff_not_hitsWithin
      (A.component d) P ε K).1 hfail (hsolve d P hmem)
  · intro h A
    by_contra hnone
    push Not at hnone
    apply h A
    intro d P hmem
    by_contra hnot
    have hfail : DeterministicFullOracleComponent.FailsWithin
        (A.component d) P ε K :=
      (DeterministicFullOracleComponent.failsWithin_iff_not_hitsWithin
        (A.component d) P ε K).2 hnot
    exact hnone d P hmem hfail

end

end WeaklyConvexLowerBound

