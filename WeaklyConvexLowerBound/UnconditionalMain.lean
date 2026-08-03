import WeaklyConvexLowerBound.PaperClass
import WeaklyConvexLowerBound.ConcretePositiveBridge
import WeaklyConvexLowerBound.ZeroActivationLocality

/-!
# Unconditional deterministic full-oracle lower bound

This module removes the two provisional analytic parameters from the earlier
assembly.  Condition (C2) is supplied by the direct two-sided segment proof
in `ZeroActivationLocality`; condition (C3) is supplied by the proved
positive-activation semantic bridge in `ConcretePositiveBridge`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-! ## Unconditional normalized and scaled certificates -/

/-- The normalized hard instance satisfies C1--C4 with its literal full
subdifferential and genuine selected half-Moreau residual. -/
def concreteHardInstanceCertificate_unconditional {M N : Nat}
    (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ)) :
    HardInstanceCertificate M N where
  admissible := hA
  f := hardValue
  oracle := fullSubdiff 1 hardValue
  stationarity := P.stationarity
  L := relayDelay N
  H := horizon M N
  finite_valued := hardValue_finite_valued
  bounded_below := hardValue_range_bddBelow hA.N_pos
  one_lipschitz := hardValue_euclideanLipschitz hA
  one_weaklyConvex := hardValue_one_weaklyConvex hA
  locality := hardValue_fullSubdiff_diagonal_locality hA
  horizon_lower := concrete_horizon_lower hA
  terminal_failure := by
    intro y hy
    exact reachable_fullSubdiff_residual_above hA hy
      (P.prox y) (P.isProx y)
  initial_gap := hardValue_initial_gap_le hA.M_ge hA.N_pos

/-- Every zero-respecting normalized query through the terminal index fails
the target stationarity threshold, with no formula hypotheses. -/
theorem concrete_zeroRespecting_failure_through_horizon_unconditional
    {M N : Nat} (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ))
    {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting
      (fullSubdiff 1 (hardValue : BlockVec M N → ℝ)) query) :
    ∀ t ≤ horizon M N,
      1 / (8 * Real.sqrt N) < P.stationarity (query t) := by
  exact (concreteHardInstanceCertificate_unconditional hA P)
    |>.query_failure_through_horizon hzr

/-- Exact paper scaling transports the unconditional normalized obstruction.
-/
theorem scaled_zeroRespecting_failure_through_horizon_unconditional
    {G rho Δ ε : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Δ))
    (P : HalfProxSelector
      (hardValue : BlockVec (parameterM G rho Δ ε) (parameterN G ε) → ℝ))
    {query : Nat →
      BlockVec (parameterM G rho Δ ε) (parameterN G ε)}
    (hzr : FullSetZeroRespecting
      (fun x => fullSubdiff rho
        (scaledFunction (G ^ 2 / rho) (rho / G)
          (hardValue : BlockVec (parameterM G rho Δ ε)
            (parameterN G ε) → ℝ)) x)
      query) :
    ∀ t ≤ horizon (parameterM G rho Δ ε) (parameterN G ε),
      ε < (P.paperScaled hG hrho).stationarity (query t) := by
  let hA := parameters_admissible hG hrho hΔ hε hacc
  have hzrBase := fullSetZeroRespecting_unscale hG hrho hzr
  have hbase := concrete_zeroRespecting_failure_through_horizon_unconditional
    hA P hzrBase
  intro t ht
  rw [paperScaled_stationarity]
  have hfail := hbase t ht
  have hthreshold := epsilon_le_terminal_threshold hG hε hA.N_pos
    (parameterN_upper hε)
  have hscaled := mul_lt_mul_of_pos_left hfail hG
  have heq : G * (1 / (8 * Real.sqrt (parameterN G ε))) =
      G / (8 * Real.sqrt (parameterN G ε)) := by ring
  rw [heq] at hscaled
  exact lt_of_le_of_lt hthreshold hscaled

/-! ## Unconditional resisting-oracle assembly -/

/-- Every deterministic component encounters a rotated member of the
selected scaled-hard subclass on which its first `paperT` queries fail. -/
theorem deterministicComponent_scaledHard_failure_unconditional
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta))
    (A : DeterministicFullOracleComponent
      (paperAmbientDim G rho Delta eps)) :
    ∃ P : FullOracleProblem (paperAmbientDim G rho Delta eps),
      SelectedScaledHardProblemClass hG hrho hDelta heps hacc
        (paperAmbientDim G rho Delta eps) P ∧
      DeterministicFullOracleComponent.FailsWithin A P eps
        (paperT G rho Delta eps) := by
  let baseOracle := paperFlattenedBaseReply G rho Delta eps
  let C := Classical.choice
    (exists_completedDynamicBatchTable
      (paperBaseDim G rho Delta eps) (paperT G rho Delta eps) A baseOracle)
  let selector := paperCanonicalRhoSelector hG hrho hDelta heps hacc
  let P : FullOracleProblem (paperAmbientDim G rho Delta eps) :=
    rotatedFullOracleProblem rho (paperScaledHardValue G rho Delta eps)
      C.finalFrame.column selector.stationarity
  have hframe : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame C.finalFrame.column :=
    C.frame_orthonormal
  have hbaseSet : ∀ z,
      (baseOracle (flatten z)).subdiff =
        flatten '' fullSubdiff rho (paperScaledHardValue G rho Delta eps) z := by
    intro z
    exact flattenedFullOracleReply_at_flatten rho
      (paperScaledHardValue G rho Delta eps) z
  have hrotated : ∀ t,
      fullOracle P (C.adaptive.query t) =
        rotateBaseReply C.finalFrame
          (baseOracle (C.finalFrame.project (C.adaptive.query t))) := by
    intro t
    exact fullOracle_rotated_eq_rotateBaseReply rho hrho.le
      (paperScaledHardValue G rho Delta eps) C.finalFrame hframe
      selector.stationarity (C.adaptive.query t)
  obtain ⟨_htranscript, hactual, hzero, hproject⟩ :=
    C.actual_transcript_and_fullSetZeroRespecting
      (fullSubdiff rho (paperScaledHardValue G rho Delta eps)) P
      hbaseSet hrotated
  have hthrough :=
    scaled_zeroRespecting_failure_through_horizon_unconditional
      hG hrho hDelta heps hacc
      (paperCanonicalHalfSelector hG hrho hDelta heps hacc) hzero
  refine ⟨P, ?_, ?_⟩
  · refine ⟨C.finalFrame.column, hframe, rfl⟩
  · intro t ht hhit
    have htH : t ≤ paperH G rho Delta eps := by
      change t < paperH G rho Delta eps + 1 at ht
      omega
    have hbaseFail := hthrough t htH
    let ti : Fin (paperT G rho Delta eps) := ⟨t, ht⟩
    have hproj := hproject ti
    have hproj' : blockProject C.finalFrame.column
        (DeterministicFullOracleComponent.queriedAt A P t) = C.blockQuery t := by
      exact hproj.symm
    change selector.stationarity
      (blockProject C.finalFrame.column
        (DeterministicFullOracleComponent.queriedAt A P t)) ≤ eps at hhit
    rw [hproj'] at hhit
    exact (not_lt_of_ge hhit) hbaseFail

/-- The concrete selected subclass has the unconditional deterministic
full-set oracle query lower bound. -/
theorem selectedScaledHard_fullOracleComplexityAtLeast_unconditional
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    FullOracleComplexityAtLeast
      (SelectedScaledHardProblemClass hG hrho hDelta heps hacc) eps
      (paperT G rho Delta eps) := by
  intro Alg
  obtain ⟨P, hmem, hfail⟩ :=
    deterministicComponent_scaledHard_failure_unconditional
      hG hrho hDelta heps hacc
        (Alg.component (paperAmbientDim G rho Delta eps))
  exact ⟨paperAmbientDim G rho Delta eps, P, hmem, hfail⟩

/-! ## Literal manuscript class -/

/-- Fully unconditional deterministic lower bound for the genuine manuscript
problem class.  The only assumptions are the stated numerical regime; there
are no residual formula, oracle-selection, or positive-activation inputs. -/
theorem paperProblemClass_fullOracleComplexityAtLeast_unconditional
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    FullOracleComplexityAtLeast (PaperProblemClass G rho Delta) eps
      (paperT G rho Delta eps) := by
  apply fullOracleComplexityAtLeast_mono
    (selectedScaledHardProblemClass_subset_paperProblemClass
      hG hrho hDelta heps hacc)
  exact selectedScaledHard_fullOracleComplexityAtLeast_unconditional
    hG hrho hDelta heps hacc

/-- The same unconditional lower bound paired with the advertised numerical
query-rate estimate. -/
theorem paperProblemClass_fullOracle_lowerBound_and_rate
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    FullOracleComplexityAtLeast (PaperProblemClass G rho Delta) eps
        (paperT G rho Delta eps) ∧
      paperC1 * (G ^ 2 * min (rho * Delta) (G ^ 2) / eps ^ 4) ≤
        (paperT G rho Delta eps : ℝ) := by
  exact ⟨paperProblemClass_fullOracleComplexityAtLeast_unconditional
      hG hrho hDelta heps hacc,
    paperT_rate_lower hG hrho hDelta heps hacc⟩

end

end WeaklyConvexLowerBound

