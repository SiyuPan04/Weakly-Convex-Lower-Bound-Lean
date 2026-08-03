import WeaklyConvexLowerBound.ConcreteCertificate
import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Unconditional positive-activation terminal bridge

The terminal proof itself forces positive activation before it invokes the
hard subgradient formula.  The semantic formula theorem can therefore be
installed here with no remaining bridge hypothesis.  Only the zero-
activation locality argument is logically separate.
-/

namespace WeaklyConvexLowerBound

noncomputable section

theorem reachable_fullSubdiff_residual_sq_above {M N : Nat}
    (hA : Admissible M N) {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y) :
    HalfMoreauResidualSqAbove
      (hardValue : BlockVec M N → ℝ) (1 / (64 * (N : ℝ))) y := by
  apply reachable_fullSubdiff_residual_sq_above_of_bridge
    hA.M_pos hA.N_pos hy (hardValue_one_weaklyConvex hA)
  intro z g hR hg
  exact fullSubdiff_one_positive_hardFormulaReply hA hR hg

theorem reachable_fullSubdiff_residual_above {M N : Nat}
    (hA : Admissible M N) {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y) :
    HalfMoreauResidualAbove (hardValue : BlockVec M N → ℝ)
      (1 / (8 * Real.sqrt (N : ℝ))) y :=
  halfMoreauResidualAbove_of_sq hA.N_pos
    (reachable_fullSubdiff_residual_sq_above hA hy)

/-- C1, C3, and C4 are now unconditional.  This certificate accepts only the
remaining all-point formula/locality statement used by C2. -/
def concreteHardInstanceCertificate_of_general {M N : Nat}
    (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        GeneralHardFormulaReply z g) :
    HardInstanceCertificate M N :=
  concreteHardInstanceCertificate hA P hgeneral
    (fun _z _g hR hg ↦
      fullSubdiff_one_positive_hardFormulaReply hA hR hg)

theorem concrete_zeroRespecting_failure_through_horizon_of_general
    {M N : Nat} (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        GeneralHardFormulaReply z g)
    {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting
      (fullSubdiff 1 (hardValue : BlockVec M N → ℝ)) query) :
    ∀ t ≤ horizon M N,
      1 / (8 * Real.sqrt N) < P.stationarity (query t) := by
  exact (concreteHardInstanceCertificate_of_general hA P hgeneral)
    |>.query_failure_through_horizon hzr

end

end WeaklyConvexLowerBound

