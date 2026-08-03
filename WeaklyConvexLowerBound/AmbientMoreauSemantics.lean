import WeaklyConvexLowerBound.ScaledMoreauSemantics
import WeaklyConvexLowerBound.Rotation

/-!
# Genuine Moreau semantics after an isometric ambient lift

This file proves that the ambient rotated envelope is the base envelope
composed with the orthogonal projection, and differentiates that literal
infimum.  It is the semantic bridge needed by the deterministic lower bound.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

def eVectorRhoProxObjective {D : Nat} (rho : ℝ) (f : EVector D → ℝ)
    (Y Z : EVector D) : ℝ :=
  f Z + rho * WeaklyConvexLowerBound.Foundation.vecSq (Z - Y)

def eVectorRhoMoreauEnvelope {D : Nat} (rho : ℝ)
    (f : EVector D → ℝ) (Y : EVector D) : ℝ :=
  sInf (Set.range (eVectorRhoProxObjective rho f Y))

def SemanticEVectorIsRhoProxPoint {D : Nat} (rho : ℝ) (f : EVector D → ℝ)
    (Y Z : EVector D) : Prop :=
  ∀ X, eVectorRhoProxObjective rho f Y Z ≤
    eVectorRhoProxObjective rho f Y X

theorem rhoMoreauEnvelope_eq_at_prox {M N : Nat} {rho : ℝ}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsRhoProxPoint rho f y z) :
    rhoMoreauEnvelope rho f y = rhoProxObjective rho f y z := by
  unfold rhoMoreauEnvelope
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨z, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact hz x

theorem eVectorRhoMoreauEnvelope_eq_at_prox {D : Nat} {rho : ℝ}
    {f : EVector D → ℝ} {Y Z : EVector D}
    (hZ : SemanticEVectorIsRhoProxPoint rho f Y Z) :
    eVectorRhoMoreauEnvelope rho f Y =
      eVectorRhoProxObjective rho f Y Z := by
  unfold eVectorRhoMoreauEnvelope
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨Z, rfl⟩
  · rintro _ ⟨X, rfl⟩
    exact hZ X

theorem IsRhoProxPoint.rotate_semantic {M N D : Nat} {rho : ℝ}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (hrho : 0 ≤ rho)
    {f : BlockVec M N → ℝ} {Y : EVector D} {z : BlockVec M N}
    (hz : IsRhoProxPoint rho f (blockProject U Y) z) :
    SemanticEVectorIsRhoProxPoint rho (rotatedValue f U) Y
      (ambientProxLift U Y z) := by
  intro X
  have hbase := hz (blockProject U X)
  have hcontract :
      blockSq (blockProject U X - blockProject U Y) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (X - Y) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  have hscaled := mul_le_mul_of_nonneg_left hcontract hrho
  unfold eVectorRhoProxObjective rotatedValue
  rw [blockProject_ambientProxLift hU,
    vecSq_ambientProxLift_sub hU]
  linarith

theorem eVectorRhoMoreauEnvelope_rotate_eq {M N D : Nat} {rho : ℝ}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (hrho : 0 ≤ rho)
    {f : BlockVec M N → ℝ} {Y : EVector D} {z : BlockVec M N}
    (hz : IsRhoProxPoint rho f (blockProject U Y) z) :
    eVectorRhoMoreauEnvelope rho (rotatedValue f U) Y =
      rhoMoreauEnvelope rho f (blockProject U Y) := by
  rw [eVectorRhoMoreauEnvelope_eq_at_prox (hz.rotate_semantic hU hrho),
    rhoMoreauEnvelope_eq_at_prox hz]
  unfold eVectorRhoProxObjective rhoProxObjective rotatedValue
  rw [blockProject_ambientProxLift hU,
    vecSq_ambientProxLift_sub hU]

/-- Projection into the hidden block frame as a continuous linear map. -/
def blockProjectCLM {M N D : Nat}
    (U : Fin (M * N) → EVector D) :
    EVector D →L[ℝ] BlockVec M N := by
  exact LinearMap.toContinuousLinearMap
    ({ toFun := blockProject U
       map_add' := blockProject_add U
       map_smul' := by
         intro c X
         ext m j
         unfold blockProject unflatten WeaklyConvexLowerBound.Foundation.frameProject
           WeaklyConvexLowerBound.Foundation.evecDotValue
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro k _
         ring } : EVector D →ₗ[ℝ] BlockVec M N)

@[simp] theorem blockProjectCLM_apply {M N D : Nat}
    (U : Fin (M * N) → EVector D) (X : EVector D) :
    blockProjectCLM U X = blockProject U X := rfl

/-- Ambient Euclidean dot-product functional. -/
def eVectorGradientCLM {D : Nat} (G : EVector D) :
    EVector D →L[ℝ] ℝ := by
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun H ↦ WeaklyConvexLowerBound.Foundation.evecDotValue G H
       map_add' := by
         intro X Y
         unfold WeaklyConvexLowerBound.Foundation.evecDotValue
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro k _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c X
         unfold WeaklyConvexLowerBound.Foundation.evecDotValue
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro k _
         ring } : EVector D →ₗ[ℝ] ℝ)

@[simp] theorem eVectorGradientCLM_apply {D : Nat}
    (G H : EVector D) :
    eVectorGradientCLM G H = WeaklyConvexLowerBound.Foundation.evecDotValue G H := rfl

theorem blockGradient_comp_project {M N D : Nat}
    (U : Fin (M * N) → EVector D) (g : BlockVec M N) :
    (blockGradientCLM g).comp (blockProjectCLM U) =
      eVectorGradientCLM (blockEmbed U g) := by
  ext H
  simp only [ContinuousLinearMap.comp_apply, blockProjectCLM_apply,
    blockGradientCLM_apply, eVectorGradientCLM_apply]
  rw [← evecDotValue_flatten]
  unfold blockEmbed blockProject
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_frameEmbed_left]
  simp only [flatten_unflatten]
  unfold WeaklyConvexLowerBound.Foundation.evecDotValue WeaklyConvexLowerBound.Foundation.frameProject
  rfl

/-- Differentiate the literal ambient infimum by combining the exact
envelope identity with the base Fréchet derivative. -/
theorem hasFDerivAt_eVectorRhoMoreauEnvelope_rotate
    {M N D : Nat} {rho : ℝ}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (hrho : 0 ≤ rho)
    {f : BlockVec M N → ℝ} {grad : BlockVec M N → BlockVec M N}
    (hprox : ∀ y, ∃ z, IsRhoProxPoint rho f y z)
    (hderiv : ∀ y, HasFDerivAt (rhoMoreauEnvelope rho f)
      (blockGradientCLM (grad y)) y)
    (Y : EVector D) :
    HasFDerivAt (eVectorRhoMoreauEnvelope rho (rotatedValue f U))
      (eVectorGradientCLM (blockEmbed U (grad (blockProject U Y)))) Y := by
  have hinner : HasFDerivAt (blockProject U) (blockProjectCLM U) Y :=
    (blockProjectCLM U).hasFDerivAt
  have hcomp := (hderiv (blockProject U Y)).comp Y hinner
  rw [blockGradient_comp_project] at hcomp
  have hfun : eVectorRhoMoreauEnvelope rho (rotatedValue f U) =
      fun X ↦ rhoMoreauEnvelope rho f (blockProject U X) := by
    funext X
    obtain ⟨z, hz⟩ := hprox (blockProject U X)
    exact eVectorRhoMoreauEnvelope_rotate_eq hU hrho hz
  rw [hfun]
  exact hcomp

def paperScaledHardProx {M N : Nat} {G rho : ℝ}
    (hA : Admissible M N) (x : BlockVec M N) : BlockVec M N :=
  unscaleVec (rho / G)
    (halfProxMap (hardValueHalfProxExistence hA)
      (scaleVec (rho / G) x))

theorem paperScaledHardProx_spec {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hA : Admissible M N)
    (x : BlockVec M N) :
    IsRhoProxPoint rho
      (scaledFunction (G ^ 2 / rho) (rho / G) (@hardValue M N)) x
      (paperScaledHardProx (G := G) (rho := rho) hA x) := by
  have hp := (halfProxMap_spec (hardValueHalfProxExistence hA)
    (scaleVec (rho / G) x)).scaled
      (amp := G ^ 2 / rho) (scale := rho / G)
      (by positivity) (div_ne_zero hrho.ne' hG.ne') x rfl
  rw [(paper_scaling_coefficients hG.ne' hrho.ne').2] at hp
  exact hp

def ambientPaperScaledHardMoreauGradient {M N D : Nat}
    (U : Fin (M * N) → EVector D) {G rho : ℝ}
    (hA : Admissible M N) (Y : EVector D) : EVector D :=
  blockEmbed U
    (scaledMoreauGradient (G ^ 2 / rho) (rho / G)
      (hardValueHalfProxExistence hA) (blockProject U Y))

/-- Final semantic theorem: the vector used by the deterministic obstruction
is the actual Fréchet gradient of the manuscript's ambient Moreau envelope. -/
theorem hasFDerivAt_ambientPaperScaledHard_moreau {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {G rho : ℝ} (hG : 0 < G) (hrho : 0 < rho)
    (hA : Admissible M N) (Y : EVector D) :
    HasFDerivAt
      (eVectorRhoMoreauEnvelope rho
        (rotatedValue
          (scaledFunction (G ^ 2 / rho) (rho / G) (@hardValue M N)) U))
      (eVectorGradientCLM
        (ambientPaperScaledHardMoreauGradient U
          (G := G) (rho := rho) hA Y)) Y := by
  apply hasFDerivAt_eVectorRhoMoreauEnvelope_rotate hU hrho.le
  · intro y
    exact ⟨paperScaledHardProx (G := G) (rho := rho) hA y,
      paperScaledHardProx_spec hG hrho hA y⟩
  · intro y
    exact hasFDerivAt_paperScaled_hardValue_moreau hG hrho hA y

def eVectorEuclideanNorm {D : Nat} (X : EVector D) : ℝ :=
  Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq X)

theorem eVectorEuclideanNorm_sq {D : Nat} (X : EVector D) :
    eVectorEuclideanNorm X ^ 2 = WeaklyConvexLowerBound.Foundation.vecSq X := by
  apply Real.sq_sqrt
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  positivity

theorem ambientPaperScaledHard_gradient_norm_sq {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {G rho : ℝ} (hG : 0 < G) (hrho : 0 < rho)
    (hA : Admissible M N) (Y : EVector D) :
    eVectorEuclideanNorm
        (ambientPaperScaledHardMoreauGradient U
          (G := G) (rho := rho) hA Y) ^ 2 =
      G ^ 2 * blockSq
        (halfProxResidual (scaleVec (rho / G) (blockProject U Y))
          (halfProxMap (hardValueHalfProxExistence hA)
            (scaleVec (rho / G) (blockProject U Y)))) := by
  rw [eVectorEuclideanNorm_sq]
  unfold ambientPaperScaledHardMoreauGradient
  rw [blockSq_blockEmbed hU]
  rw [← blockEuclideanNorm_sq]
  exact paperScaled_hardValue_gradient_norm_sq hG hrho hA (blockProject U Y)

end

end WeaklyConvexLowerBound

