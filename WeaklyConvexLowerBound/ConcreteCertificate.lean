import WeaklyConvexLowerBound.ConcreteLocality
import WeaklyConvexLowerBound.ConcreteTerminal
import WeaklyConvexLowerBound.Regularity

/-!
# Concrete normalized C1--C4 certificate

The only two analytic inputs below are the two directions of the exact hard
subdifferential formula.  All finite-dimensional, filtration, proximal, and
constant arithmetic is discharged here.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- An explicit selection of a global minimizer of every half-proximal
problem.  `MoreauSemantics` constructs this selector and proves that its
residual is the Moreau-envelope gradient. -/
structure HalfProxSelector {M N : Nat} (f : BlockVec M N → ℝ) where
  prox : BlockVec M N → BlockVec M N
  isProx : ∀ y, IsHalfProxPoint f y (prox y)

def HalfProxSelector.stationarity {M N : Nat} {f : BlockVec M N → ℝ}
    (P : HalfProxSelector f) (y : BlockVec M N) : ℝ :=
  Real.sqrt (blockSq (halfProxResidual y (P.prox y)))

theorem concrete_horizon_lower {M N : Nat} (hA : Admissible M N) :
    M * N ≤ 120 * horizon M N := by
  have hreal := product_over_120_le_horizon hA.M_ge hA.N_ge
  have hreal' : ((M * N : Nat) : ℝ) ≤
      120 * (horizon M N : ℝ) := by
    linarith
  exact_mod_cast hreal'

/-- Assemble the literal hard instance as the normalized certificate used by
the abstract zero-respecting induction. -/
def concreteHardInstanceCertificate {M N : Nat}
    (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        HardFormulaReply z g) :
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
  locality := hardValue_fullSubdiff_locality_of_formula_inclusion hA hgeneral
  horizon_lower := concrete_horizon_lower hA
  terminal_failure := by
    intro y hy
    have hall := reachable_fullSubdiff_residual_above_of_bridge
      hA.M_pos hA.N_pos hy (hardValue_one_weaklyConvex hA) hpositive
    exact hall (P.prox y) (P.isProx y)
  initial_gap := hardValue_initial_gap_le hA.M_ge hA.N_pos

/-- Normalized queried-point lower bound, with the off-by-one convention
fully explicit, for the concrete set-valued full oracle. -/
theorem concrete_zeroRespecting_failure_through_horizon {M N : Nat}
    (hA : Admissible M N)
    (P : HalfProxSelector (hardValue : BlockVec M N → ℝ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        HardFormulaReply z g)
    {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting
      (fullSubdiff 1 (hardValue : BlockVec M N → ℝ)) query) :
    ∀ t ≤ horizon M N,
      1 / (8 * Real.sqrt N) < P.stationarity (query t) := by
  exact (concreteHardInstanceCertificate hA P hgeneral hpositive)
    |>.query_failure_through_horizon hzr

end

end WeaklyConvexLowerBound

