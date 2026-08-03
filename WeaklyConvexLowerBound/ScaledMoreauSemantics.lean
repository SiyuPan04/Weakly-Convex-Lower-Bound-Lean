import WeaklyConvexLowerBound.MoreauSemantics
import WeaklyConvexLowerBound.ExactScaling
import Mathlib.Data.Real.Pointwise

/-!
# Genuine Moreau semantics under the paper scaling

The terminal certificate is written with a proximal residual.  This file
identifies that residual with the Fréchet gradient of the literal scaled
infimal-convolution envelope, rather than introducing stationarity by
definition.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- Proximal objective with arbitrary positive quadratic coefficient. -/
def rhoProxObjective {M N : Nat} (rho : ℝ) (f : BlockVec M N → ℝ)
    (y z : BlockVec M N) : ℝ :=
  f z + rho * blockSq (z - y)

/-- The literal Moreau envelope used in the manuscript when the weak
convexity modulus is `rho`. -/
def rhoMoreauEnvelope {M N : Nat} (rho : ℝ) (f : BlockVec M N → ℝ)
    (y : BlockVec M N) : ℝ :=
  sInf (Set.range (rhoProxObjective rho f y))

@[simp] theorem isRhoProxPoint_iff {M N : Nat} {rho : ℝ}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N} :
    IsRhoProxPoint rho f y z ↔
      ∀ x, rhoProxObjective rho f y z ≤ rhoProxObjective rho f y x := by
  rfl

/-- Multiplication of every block coordinate is a continuous linear map. -/
def scaleVecCLM {M N : Nat} (a : ℝ) :
    BlockVec M N →L[ℝ] BlockVec M N :=
  a • ContinuousLinearMap.id ℝ (BlockVec M N)

@[simp] theorem scaleVecCLM_apply {M N : Nat} (a : ℝ)
    (x : BlockVec M N) :
    scaleVecCLM a x = scaleVec a x := by
  rfl

theorem scaleVec_surjective {M N : Nat} {a : ℝ} (ha : a ≠ 0) :
    Function.Surjective (scaleVec (M := M) (N := N) a) := by
  intro z
  exact ⟨unscaleVec a z, scaleVec_unscaleVec ha z⟩

/-- The scaled proximal objective is exactly a positive multiple of the base
half-proximal objective after the coordinate bijection. -/
theorem rhoProxObjective_scaled {M N : Nat} {amp scale : ℝ}
    (f : BlockVec M N → ℝ)
    (x u : BlockVec M N) :
    rhoProxObjective (amp * scale ^ 2) (scaledFunction amp scale f) x u =
      amp * halfProxObjective f (scaleVec scale x) (scaleVec scale u) := by
  unfold rhoProxObjective scaledFunction halfProxObjective
  rw [scaleVec_sub, blockSq_scaleVec]
  ring

/-- Exact equality between the literal scaled Moreau envelope and the scaled
base half-Moreau envelope. -/
theorem rhoMoreauEnvelope_scaled {M N : Nat} {amp scale : ℝ}
    (hamp : 0 ≤ amp) (hscale : scale ≠ 0)
    (f : BlockVec M N → ℝ) (x : BlockVec M N) :
    rhoMoreauEnvelope (amp * scale ^ 2) (scaledFunction amp scale f) x =
      amp * halfMoreauEnvelope f (scaleVec scale x) := by
  unfold rhoMoreauEnvelope halfMoreauEnvelope
  have hfun :
      (fun u : BlockVec M N ↦
        rhoProxObjective (amp * scale ^ 2)
          (scaledFunction amp scale f) x u) =
      (fun u : BlockVec M N ↦
        amp * halfProxObjective f (scaleVec scale x) (scaleVec scale u)) := by
    funext u
    exact rhoProxObjective_scaled f x u
  change sInf (Set.range (fun u : BlockVec M N ↦
    rhoProxObjective (amp * scale ^ 2)
      (scaledFunction amp scale f) x u)) = _
  rw [hfun]
  have hrange :
      Set.range (fun u : BlockVec M N ↦
        amp * halfProxObjective f (scaleVec scale x) (scaleVec scale u)) =
      Set.range (fun z : BlockVec M N ↦
        amp * halfProxObjective f (scaleVec scale x) z) := by
    apply Set.Subset.antisymm
    · rintro r ⟨u, rfl⟩
      exact ⟨scaleVec scale u, rfl⟩
    · rintro r ⟨z, rfl⟩
      obtain ⟨u, rfl⟩ := scaleVec_surjective hscale z
      exact ⟨u, rfl⟩
  rw [hrange]
  change (⨅ z : BlockVec M N,
      amp • halfProxObjective f (scaleVec scale x) z) =
    amp • (⨅ z : BlockVec M N,
      halfProxObjective f (scaleVec scale x) z)
  exact (Real.smul_iInf_of_nonneg hamp _).symm

/-- The vector representing the derivative of the scaled envelope. -/
def scaledMoreauGradient {M N : Nat} {f : BlockVec M N → ℝ}
    (amp scale : ℝ) (hexists : HasHalfProxEverywhere f)
    (x : BlockVec M N) : BlockVec M N :=
  (amp * scale) • halfMoreauGradient hexists (scaleVec scale x)

theorem scaledGradientCLM_identity {M N : Nat} (amp scale : ℝ)
    (g : BlockVec M N) :
    amp • ((blockGradientCLM g).comp (scaleVecCLM scale)) =
      blockGradientCLM ((amp * scale) • g) := by
  ext h
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    blockGradientCLM_apply, scaleVecCLM_apply, blockDot_scaleVec_right,
    blockDot_smul_left]
  ring

/-- The genuine scaled envelope has the Fréchet derivative represented by
the exactly scaled proximal residual. -/
theorem hasFDerivAt_rhoMoreauEnvelope_scaled {M N : Nat}
    {f : BlockVec M N → ℝ} {amp scale : ℝ}
    (hweak : WeaklyConvex 1 f) (hexists : HasHalfProxEverywhere f)
    (hamp : 0 ≤ amp) (hscale : scale ≠ 0) (x : BlockVec M N) :
    HasFDerivAt
      (rhoMoreauEnvelope (amp * scale ^ 2) (scaledFunction amp scale f))
      (blockGradientCLM (scaledMoreauGradient amp scale hexists x)) x := by
  have hinner : HasFDerivAt (scaleVec (M := M) (N := N) scale)
      (scaleVecCLM scale) x := (scaleVecCLM scale).hasFDerivAt
  have houter := (hasFDerivAt_halfMoreauEnvelope hweak hexists
    (scaleVec scale x)).comp x hinner
  have hmul := houter.const_mul amp
  rw [scaledGradientCLM_identity] at hmul
  have hfun :
      rhoMoreauEnvelope (amp * scale ^ 2) (scaledFunction amp scale f) =
        fun y ↦ amp * halfMoreauEnvelope f (scaleVec scale y) := by
    funext y
    exact rhoMoreauEnvelope_scaled hamp hscale f y
  rw [hfun]
  exact hmul

theorem scaledMoreauGradient_eq_residual {M N : Nat}
    {f : BlockVec M N → ℝ} {amp scale : ℝ}
    (hweak : WeaklyConvex 1 f) (hexists : HasHalfProxEverywhere f)
    (x : BlockVec M N) :
    scaledMoreauGradient amp scale hexists x =
      rhoResidual (amp * scale ^ 2) x
        (unscaleVec scale (halfProxMap hexists (scaleVec scale x))) := by
  rw [rhoResidual_scaled]
  unfold scaledMoreauGradient
  rw [halfMoreauGradient_eq_residual_of_prox hweak hexists
    (halfProxMap_spec hexists (scaleVec scale x))]

/-- Selection-free squared-norm equality for the true scaled Moreau
gradient. -/
theorem scaledMoreauGradient_norm_sq_of_base_prox {M N : Nat}
    {f : BlockVec M N → ℝ} {amp scale : ℝ}
    (hweak : WeaklyConvex 1 f) (hexists : HasHalfProxEverywhere f)
    {x zbar : BlockVec M N} (hz : IsHalfProxPoint f (scaleVec scale x) zbar) :
    blockEuclideanNorm (scaledMoreauGradient amp scale hexists x) ^ 2 =
      blockSq (rhoResidual (amp * scale ^ 2) x (unscaleVec scale zbar)) := by
  rw [blockEuclideanNorm_sq, rhoResidual_scaled]
  unfold scaledMoreauGradient
  rw [halfMoreauGradient_eq_residual_of_prox hweak hexists hz]

/-- Paper coefficients: the literal `rho`-Moreau envelope of the scaled hard
instance has derivative vector equal to `G` times the normalized residual. -/
theorem hasFDerivAt_paperScaled_hardValue_moreau {M N : Nat}
    {G rho : ℝ} (hG : 0 < G) (hrho : 0 < rho)
    (hA : Admissible M N) (x : BlockVec M N) :
    HasFDerivAt
      (rhoMoreauEnvelope rho
        (scaledFunction (G ^ 2 / rho) (rho / G) (@hardValue M N)))
      (blockGradientCLM
        (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
          (hardValueHalfProxExistence hA) x)) x := by
  have h := hasFDerivAt_rhoMoreauEnvelope_scaled
    (hardValue_one_weaklyConvex hA) (hardValueHalfProxExistence hA)
    (amp := G ^ 2 / rho) (scale := rho / G)
    (by positivity) (div_ne_zero hrho.ne' hG.ne') x
  rw [(paper_scaling_coefficients hG.ne' hrho.ne').2] at h
  exact h

theorem paperScaled_hardValue_gradient_norm_sq {M N : Nat}
    {G rho : ℝ} (hG : 0 < G) (hrho : 0 < rho)
    (hA : Admissible M N) (x : BlockVec M N) :
    blockEuclideanNorm
        (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
          (hardValueHalfProxExistence hA) x) ^ 2 =
      G ^ 2 * blockSq
        (halfProxResidual (scaleVec (rho / G) x)
          (halfProxMap (hardValueHalfProxExistence hA)
            (scaleVec (rho / G) x))) := by
  rw [blockEuclideanNorm_sq]
  unfold scaledMoreauGradient
  change blockSq (scaleVec ((G ^ 2 / rho) * (rho / G))
      (halfMoreauGradient (hardValueHalfProxExistence hA)
        (scaleVec (rho / G) x))) = _
  rw [blockSq_scaleVec]
  rw [(paper_scaling_coefficients hG.ne' hrho.ne').1]
  rfl

end

end WeaklyConvexLowerBound

