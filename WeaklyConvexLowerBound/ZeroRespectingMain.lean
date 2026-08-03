import WeaklyConvexLowerBound.UnconditionalMain
import WeaklyConvexLowerBound.ScaledMoreauSemantics
import WeaklyConvexLowerBound.PaperClass

/-!
# The fixed-function zero-respecting main theorem

This module packages the zero-respecting statement in the quantifier order
used by the manuscript: one fixed scaled hard function is chosen first, and
then every generalized full-set zero-respecting query sequence is obstructed
through the common terminal horizon.  The stationarity measure below is the
norm of the vector representing the Frechet derivative of the literal Moreau
envelope, not an abstract selector field.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- The explicit vector representing the derivative of the literal
`rho`-Moreau envelope of the fixed paper-scaled hard function. -/
def paperZeroRespectingMoreauGradient
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    BlockVec (paperM G rho Delta eps) (paperN G eps) →
      BlockVec (paperM G rho Delta eps) (paperN G eps) :=
  scaledMoreauGradient (G ^ 2 / rho) (rho / G)
    (hardValueHalfProxExistence
      (parameters_admissible hG hrho hDelta heps hacc))

/-- The canonical selected residual of the fixed scaled hard function is
exactly the norm of its genuine Moreau-envelope gradient vector. -/
theorem paperCanonicalStationarity_eq_trueMoreauGradientNorm
    {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hA : Admissible M N)
    (x : BlockVec M N) :
    ((canonicalHardValueSelector hA).paperScaled hG hrho).stationarity x =
      blockEuclideanNorm
        (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
          (hardValueHalfProxExistence hA) x) := by
  let d := halfProxResidual
    (scaleVec (rho / G) x)
    (halfProxMap (hardValueHalfProxExistence hA)
      (scaleVec (rho / G) x))
  have hleft :
      ((canonicalHardValueSelector hA).paperScaled hG hrho).stationarity x =
        G * Real.sqrt (blockSq d) := by
    have hs := paperScaled_stationarity hG hrho
      (canonicalHardValueSelector hA) x
    simpa [canonicalHardValueSelector, HalfProxSelector.stationarity, d]
      using hs
  have hleftSq :
      (((canonicalHardValueSelector hA).paperScaled hG hrho).stationarity x) ^ 2 =
        G ^ 2 * blockSq d := by
    rw [hleft, mul_pow, Real.sq_sqrt (blockSq_nonneg d)]
  have hrightSq := paperScaled_hardValue_gradient_norm_sq hG hrho hA x
  change blockEuclideanNorm
      (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
        (hardValueHalfProxExistence hA) x) ^ 2 =
      G ^ 2 * blockSq d at hrightSq
  have hleftNonneg : 0 ≤
      ((canonicalHardValueSelector hA).paperScaled hG hrho).stationarity x := by
    unfold RhoProxSelector.stationarity
    exact Real.sqrt_nonneg _
  have hrightNonneg : 0 ≤ blockEuclideanNorm
      (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
        (hardValueHalfProxExistence hA) x) := by
    unfold blockEuclideanNorm
    exact Real.sqrt_nonneg _
  nlinarith

/-- A direct formal statement of the fixed-function zero-respecting theorem.
The dimensions, objective, set-valued oracle, envelope, gradient vector, and
horizon are all the literal paper objects appearing in the field types. -/
structure ZeroRespectingMainStatement
    (G rho Delta eps : ℝ)
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) : Prop where
  admissible : Admissible (paperM G rho Delta eps) (paperN G eps)
  rho_weaklyConvex :
    WeaklyConvex rho (paperScaledHardValue G rho Delta eps)
  G_lipschitz :
    EuclideanLipschitz G (paperScaledHardValue G rho Delta eps)
  bounded_below :
    BddBelow (Set.range (paperScaledHardValue G rho Delta eps))
  initial_gap :
    paperScaledHardValue G rho Delta eps 0 -
      sInf (Set.range (paperScaledHardValue G rho Delta eps)) ≤ Delta
  literal_moreau_gradient : ∀ x,
    HasFDerivAt
      (rhoMoreauEnvelope rho (paperScaledHardValue G rho Delta eps))
      (blockGradientCLM
        (paperZeroRespectingMoreauGradient
          hG hrho hDelta heps hacc x)) x
  all_fullSetZeroRespecting_queries_fail :
    ∀ query : Nat →
        BlockVec (paperM G rho Delta eps) (paperN G eps),
      FullSetZeroRespecting
          (fullSubdiff rho (paperScaledHardValue G rho Delta eps)) query →
        ∀ t ≤ paperH G rho Delta eps,
          eps < blockEuclideanNorm
            (paperZeroRespectingMoreauGradient
              hG hrho hDelta heps hacc (query t))
  horizon_rate :
    paperC1 * (G ^ 2 * min (rho * Delta) (G ^ 2) / eps ^ 4) ≤
      (paperH G rho Delta eps : ℝ)

/-- Unconditional fixed-function version of the manuscript's main
zero-respecting theorem.  There are no residual subdifferential-formula or
oracle-selection hypotheses. -/
theorem zeroRespectingMain
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    ZeroRespectingMainStatement
      G rho Delta eps hG hrho hDelta heps hacc := by
  let hA := parameters_admissible hG hrho hDelta heps hacc
  refine {
    admissible := hA
    rho_weaklyConvex := ?_
    G_lipschitz := ?_
    bounded_below := paperScaledHardValue_bddBelow
      hG hrho hDelta heps hacc
    initial_gap := paperScaledHardValue_initialGap_le
      hG hrho hDelta heps hacc
    literal_moreau_gradient := ?_
    all_fullSetZeroRespecting_queries_fail := ?_
    horizon_rate := ?_ }
  · dsimp [paperScaledHardValue]
    exact weaklyConvex_paper_scaled hG hrho
      (hardValue_one_weaklyConvex hA)
  · dsimp [paperScaledHardValue]
    have hlip := euclideanLipschitz_scaled
      (amp := G ^ 2 / rho) (scale := rho / G)
      (hardValue_euclideanLipschitz hA)
    rw [(paper_scaling_coefficients hG.ne' hrho.ne').1] at hlip
    simpa using hlip
  · intro x
    exact hasFDerivAt_paperScaled_hardValue_moreau hG hrho hA x
  · intro query hzr t ht
    have hzr' : FullSetZeroRespecting
        (fun x => fullSubdiff rho
          (scaledFunction (G ^ 2 / rho) (rho / G)
            (hardValue : BlockVec (paperM G rho Delta eps)
              (paperN G eps) → ℝ)) x) query := by
      simpa [paperScaledHardValue] using hzr
    have hfail := scaled_zeroRespecting_failure_through_horizon_unconditional
      hG hrho hDelta heps hacc
      (canonicalHardValueSelector hA) hzr'
    have hstationarity : eps <
        ((canonicalHardValueSelector hA).paperScaled hG hrho).stationarity
          (query t) := hfail t ht
    rw [paperCanonicalStationarity_eq_trueMoreauGradientNorm
      hG hrho hA (query t)] at hstationarity
    simpa [paperZeroRespectingMoreauGradient, hA] using hstationarity
  · exact selected_horizon_rate_lower hG hrho hDelta heps hacc

end

end WeaklyConvexLowerBound

