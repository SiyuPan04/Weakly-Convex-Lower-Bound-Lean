import WeaklyConvexLowerBound.UnconditionalMain
import WeaklyConvexLowerBound.OutputAugmentation

/-!
# Arbitrary deterministic outputs for the manuscript class

The resisting-oracle theorem controls queried points.  The standard
output-as-an-extra-query reduction turns that statement into a lower bound
for an arbitrary deterministic, transcript-dependent returned point.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- A full-oracle lower bound through `K` queries also holds through every
shorter query horizon `L`. -/
theorem fullOracleComplexityAtLeast_of_le
    {C : DimensionedProblemClass} {epsilon : Real} {K L : Nat}
    (hLK : L ≤ K) (hlower : FullOracleComplexityAtLeast C epsilon K) :
    FullOracleComplexityAtLeast C epsilon L := by
  intro A
  obtain ⟨d, P, hP, hfail⟩ := hlower A
  refine ⟨d, P, hP, ?_⟩
  intro t ht
  exact hfail t (lt_of_lt_of_le ht hLK)

/-- The selected hard horizon is positive throughout the manuscript's
admissible numerical regime. -/
theorem paperH_pos
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    0 < paperH G rho Delta eps := by
  have hA := parameters_admissible hG hrho hDelta heps hacc
  change 0 < horizon (paperM G rho Delta eps) (paperN G eps)
  unfold horizon
  have hNge : 60 ≤ paperN G eps := hA.N_ge
  have hN : 0 < paperN G eps / 2 := Nat.div_pos (by omega) (by omega)
  omega

/-- For every positive number `T` of replies strictly below the paper query
horizon, an arbitrary deterministic function of those replies can still be
forced to return a non-`epsilon`-stationary point of a problem in the literal
manuscript class. -/
theorem paperProblemClass_outputAt_failure_before_paperT
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta))
    {T : Nat} (hTpos : 0 < T) (hTpaper : T < paperT G rho Delta eps) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, PaperProblemClass G rho Delta d P ∧
        ¬ P.stationarity ((A.component d).outputAt P T) ≤ eps := by
  have hlower := paperProblemClass_fullOracleComplexityAtLeast_unconditional
    hG hrho hDelta heps hacc
  have hshort : FullOracleComplexityAtLeast
      (PaperProblemClass G rho Delta) eps (T + 1) :=
    fullOracleComplexityAtLeast_of_le (by omega) hlower
  exact outputAt_failure_of_fullOracleComplexityAtLeast hTpos hshort

/-- Even an arbitrary fixed point returned before receiving any reply can
be defeated.  It is installed as query `1` after the model's mandatory zero
query. -/
theorem paperProblemClass_outputAt_failure_at_zero
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, PaperProblemClass G rho Delta d P ∧
        ¬ P.stationarity ((A.component d).outputAt P 0) ≤ eps := by
  have hlower := paperProblemClass_fullOracleComplexityAtLeast_unconditional
    hG hrho hDelta heps hacc
  have htwo : FullOracleComplexityAtLeast
      (PaperProblemClass G rho Delta) eps 2 :=
    fullOracleComplexityAtLeast_of_le (by
      have hH := paperH_pos hG hrho hDelta heps hacc
      change 2 ≤ paperH G rho Delta eps + 1
      omega) hlower
  exact outputAt_zero_failure_of_fullOracleComplexityAtLeast_two htwo

/-- Unified arbitrary-output endpoint, including the zero-reply case. -/
theorem paperProblemClass_outputAt_failure_before_paperT_all
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta))
    {T : Nat} (hTpaper : T < paperT G rho Delta eps) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, PaperProblemClass G rho Delta d P ∧
        ¬ P.stationarity ((A.component d).outputAt P T) ≤ eps := by
  by_cases hT : T = 0
  · subst T
    exact paperProblemClass_outputAt_failure_at_zero
      hG hrho hDelta heps hacc
  · exact paperProblemClass_outputAt_failure_before_paperT
      hG hrho hDelta heps hacc (Nat.pos_of_ne_zero hT) hTpaper

/-- In particular, the arbitrary output formed after the first `paperH`
replies fails.  The extra queried output has index `paperH`, while
`paperT = paperH + 1` is the corresponding query count. -/
theorem paperProblemClass_outputAt_failure_at_paperH
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    ∀ A : DimensionWiseFullOracleAlgorithm,
      ∃ d P, PaperProblemClass G rho Delta d P ∧
        ¬ P.stationarity
            ((A.component d).outputAt P (paperH G rho Delta eps)) ≤ eps := by
  have hHpos : 0 < paperH G rho Delta eps :=
    paperH_pos hG hrho hDelta heps hacc
  exact paperProblemClass_outputAt_failure_before_paperT
    hG hrho hDelta heps hacc hHpos
      (Nat.lt_succ_self (paperH G rho Delta eps))

end

end WeaklyConvexLowerBound

