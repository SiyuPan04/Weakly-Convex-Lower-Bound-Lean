import WeaklyConvexLowerBound.ConcreteCertificate
import WeaklyConvexLowerBound.ScalingFullSubdiff
import WeaklyConvexLowerBound.Scaling

/-!
# Scaled zero-respecting lower bound

This module transports the normalized hard instance, its complete set-valued
oracle, proximal stationarity, and the zero-respecting rule through the exact
paper scaling.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- A selector for the Moreau proximal objective with quadratic coefficient
`rho`. -/
structure RhoProxSelector {M N : Nat} (rho : ℝ)
    (f : BlockVec M N → ℝ) where
  prox : BlockVec M N → BlockVec M N
  isProx : ∀ x, IsRhoProxPoint rho f x (prox x)

def RhoProxSelector.stationarity {M N : Nat} {rho : ℝ}
    {f : BlockVec M N → ℝ} (P : RhoProxSelector rho f)
    (x : BlockVec M N) : ℝ :=
  Real.sqrt (blockSq (rhoResidual rho x (P.prox x)))

/-- The base half-prox selector induces the selected proximal point of the
scaled objective. -/
def HalfProxSelector.scaled {M N : Nat} {amp scale : ℝ}
    (hamp : 0 ≤ amp) (hscale : scale ≠ 0)
    {f : BlockVec M N → ℝ} (P : HalfProxSelector f) :
    RhoProxSelector (amp * scale ^ 2) (scaledFunction amp scale f) where
  prox := fun x => unscaleVec scale (P.prox (scaleVec scale x))
  isProx := by
    intro x
    exact (P.isProx (scaleVec scale x)).scaled
      hamp hscale x rfl

theorem scaledSelector_residual {M N : Nat} {amp scale : ℝ}
    (hamp : 0 ≤ amp) (hscale : scale ≠ 0)
    {f : BlockVec M N → ℝ} (P : HalfProxSelector f)
    (x : BlockVec M N) :
    rhoResidual (amp * scale ^ 2) x
        ((P.scaled hamp hscale).prox x) =
      (amp * scale) •
        halfProxResidual (scaleVec scale x) (P.prox (scaleVec scale x)) := by
  exact rhoResidual_scaled amp scale x (P.prox (scaleVec scale x))

theorem scaledSelector_stationarity {M N : Nat} {amp scale : ℝ}
    (hamp : 0 ≤ amp) (hscale : scale ≠ 0)
    {f : BlockVec M N → ℝ} (P : HalfProxSelector f)
    (x : BlockVec M N) :
    (P.scaled hamp hscale).stationarity x =
      |amp * scale| * P.stationarity (scaleVec scale x) := by
  let d := halfProxResidual (scaleVec scale x) (P.prox (scaleVec scale x))
  have hres := scaledSelector_residual hamp hscale P x
  have hsq : blockSq (rhoResidual (amp * scale ^ 2) x
      ((P.scaled hamp hscale).prox x)) =
      (amp * scale) ^ 2 * blockSq d := by
    rw [hres]
    change blockSq (scaleVec (amp * scale) d) = _
    exact blockSq_scaleVec (amp * scale) d
  unfold RhoProxSelector.stationarity HalfProxSelector.stationarity
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Positive coordinate scaling preserves the full-set zero-respecting rule,
using equality of the *entire* scaled oracle reply. -/
theorem fullSetZeroRespecting_unscale {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting
      (fun x => fullSubdiff rho
        (scaledFunction (G ^ 2 / rho) (rho / G) f) x) query) :
    FullSetZeroRespecting
      (fun z => fullSubdiff 1 f z)
      (fun t => scaleVec (rho / G) (query t)) := by
  constructor
  · rw [hzr.start]
    ext m j
    simp [scaleVec]
  · intro t p hp
    have hx : query t p.1 p.2 ≠ 0 := by
      intro hx0
      apply hp
      simp [scaleVec, hx0]
    obtain ⟨s, hst, gs, hgs, hcoord⟩ := hzr.respects t p hx
    rw [fullSubdiff_paper_scaled_eq hG hrho] at hgs
    obtain ⟨g, hg, rfl⟩ := hgs
    refine ⟨s, hst, g, hg, ?_⟩
    intro hg0
    apply hcoord
    simp [hg0]

/-- Paper-specific selector with coefficient exactly `rho`. -/
def HalfProxSelector.paperScaled {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (P : HalfProxSelector f) :
    RhoProxSelector rho (scaledFunction (G ^ 2 / rho) (rho / G) f) where
  prox := fun x => unscaleVec (rho / G)
    (P.prox (scaleVec (rho / G) x))
  isProx := by
    intro x
    have hp := (P.isProx (scaleVec (rho / G) x)).scaled
      (amp := G ^ 2 / rho) (scale := rho / G)
      (by positivity) (div_ne_zero hrho.ne' hG.ne') x rfl
    rw [(paper_scaling_coefficients hG.ne' hrho.ne').2] at hp
    exact hp

theorem paperScaled_stationarity {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (P : HalfProxSelector f)
    (x : BlockVec M N) :
    (P.paperScaled hG hrho).stationarity x =
      G * P.stationarity (scaleVec (rho / G) x) := by
  have hcoef := paper_scaling_coefficients hG.ne' hrho.ne'
  have hres : rhoResidual rho x ((P.paperScaled hG hrho).prox x) =
      ((G ^ 2 / rho) * (rho / G)) •
        halfProxResidual (scaleVec (rho / G) x)
          (P.prox (scaleVec (rho / G) x)) := by
    change rhoResidual rho x
        (unscaleVec (rho / G) (P.prox (scaleVec (rho / G) x))) = _
    calc
      _ = rhoResidual ((G ^ 2 / rho) * (rho / G) ^ 2) x
          (unscaleVec (rho / G) (P.prox (scaleVec (rho / G) x))) := by
        rw [hcoef.2]
      _ = _ := rhoResidual_scaled (G ^ 2 / rho) (rho / G) x
        (P.prox (scaleVec (rho / G) x))
  unfold RhoProxSelector.stationarity HalfProxSelector.stationarity
  rw [hres]
  change Real.sqrt (blockSq (scaleVec ((G ^ 2 / rho) * (rho / G))
      (halfProxResidual (scaleVec (rho / G) x)
        (P.prox (scaleVec (rho / G) x))))) = _
  rw [blockSq_scaleVec, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, hcoef.1, abs_of_pos hG]

/-- End-to-end scaled queried-point obstruction. -/
theorem scaled_zeroRespecting_failure_through_horizon
    {G rho Δ ε : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Δ))
    (P : HalfProxSelector
      (hardValue : BlockVec (parameterM G rho Δ ε) (parameterN G ε) → ℝ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (parameterM G rho Δ ε) (parameterN G ε) → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (parameterM G rho Δ ε) (parameterN G ε) → ℝ) z →
        HardFormulaReply z g)
    {query : Nat →
      BlockVec (parameterM G rho Δ ε) (parameterN G ε)}
    (hzr : FullSetZeroRespecting
      (fun x => fullSubdiff rho
        (scaledFunction (G ^ 2 / rho) (rho / G)
          (hardValue : BlockVec (parameterM G rho Δ ε) (parameterN G ε) → ℝ)) x)
      query) :
    ∀ t ≤ horizon (parameterM G rho Δ ε) (parameterN G ε),
      ε < (P.paperScaled hG hrho).stationarity (query t) := by
  let hA := parameters_admissible hG hrho hΔ hε hacc
  have hzrBase := fullSetZeroRespecting_unscale hG hrho hzr
  have hbase := concrete_zeroRespecting_failure_through_horizon
    hA P hgeneral hpositive hzrBase
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

/-- The selected horizon has the advertised numerical lower-bound scale. -/
theorem selected_horizon_rate_lower {G rho Δ ε : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Δ)) :
    paperC1 * (G ^ 2 * min (rho * Δ) (G ^ 2) / ε ^ 4) ≤
      (horizon (parameterM G rho Δ ε) (parameterN G ε) : ℝ) := by
  apply horizon_lower_bound hG hrho hΔ hε hacc
  exact product_over_120_le_horizon
    (parameterM_ge_5 hG hrho hΔ hε hacc |>.trans' (by omega))
    (parameterN_ge_60 hG hrho hΔ hε hacc)

end

end WeaklyConvexLowerBound

