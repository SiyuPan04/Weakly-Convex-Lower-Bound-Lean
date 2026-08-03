import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.QuadraticSubgradient

/-!
# Exact coordinate and proximal scaling

This is the algebraic core of Lemma `lem:scaling`.  The analytic class
closure is separated from these exact identities, so every coefficient can
be kernel-checked without appealing to informal chain rules.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

def scaleVec {M N : Nat} (a : ℝ) (x : BlockVec M N) : BlockVec M N :=
  a • x

def scaledFunction {M N : Nat} (amp scale : ℝ)
    (f : BlockVec M N → ℝ) : BlockVec M N → ℝ :=
  fun x => amp * f (scaleVec scale x)

theorem scaleVec_sub {M N : Nat} (a : ℝ) (x y : BlockVec M N) :
    scaleVec a x - scaleVec a y = scaleVec a (x - y) := by
  ext m j
  simp [scaleVec]
  ring

theorem blockSq_scaleVec {M N : Nat} (a : ℝ) (x : BlockVec M N) :
    blockSq (scaleVec a x) = a ^ 2 * blockSq x := by
  unfold blockSq scaleVec
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem blockDot_smul_right_scalar {M N : Nat} (a : ℝ)
    (x y : BlockVec M N) : blockDot x (a • y) = a * blockDot x y := by
  rw [blockDot_comm, blockDot_smul_left, blockDot_comm]

theorem blockDot_scaleVec_right {M N : Nat} (a : ℝ)
    (x y : BlockVec M N) : blockDot x (scaleVec a y) = a * blockDot x y :=
  blockDot_smul_right_scalar a x y

/-- Exact covariance of the quadratic-support subdifferential. -/
theorem qSubgradient_scaled {M N : Nat} {c amp scale : ℝ}
    {f : BlockVec M N → ℝ} {z g : BlockVec M N}
    (hamp : 0 ≤ amp) (hg : QSubgradient c f z g)
    (x : BlockVec M N) (hz : z = scaleVec scale x) :
    QSubgradient (amp * c * scale ^ 2) (scaledFunction amp scale f) x
      ((amp * scale) • g) := by
  intro y
  have hbase := hg (scaleVec scale y)
  have hscaled := mul_le_mul_of_nonneg_left hbase hamp
  rw [hz, scaleVec_sub, blockDot_scaleVec_right, blockSq_scaleVec] at hscaled
  unfold scaledFunction
  rw [blockDot_smul_left]
  nlinarith

/-- Squared Euclidean Lipschitz constants scale by `amp * scale`. -/
theorem euclideanLipschitz_scaled {M N : Nat} {C amp scale : ℝ}
    {f : BlockVec M N → ℝ} (hf : EuclideanLipschitz C f) :
    EuclideanLipschitz (amp * scale * C) (scaledFunction amp scale f) := by
  intro x y
  have h := hf (scaleVec scale x) (scaleVec scale y)
  rw [scaleVec_sub, blockSq_scaleVec] at h
  unfold scaledFunction
  nlinarith [sq_nonneg amp, sq_nonneg scale, sq_nonneg C]

/-- Proximal objective with quadratic coefficient `rho`. -/
def IsRhoProxPoint {M N : Nat} (rho : ℝ) (f : BlockVec M N → ℝ)
    (x z : BlockVec M N) : Prop :=
  ∀ y, f z + rho * blockSq (z - x) ≤ f y + rho * blockSq (y - x)

theorem isHalfProxPoint_iff_isRhoProxPoint_one {M N : Nat}
    {f : BlockVec M N → ℝ} {x z : BlockVec M N} :
    IsHalfProxPoint f x z ↔ IsRhoProxPoint 1 f x z := by
  simp [IsHalfProxPoint, IsRhoProxPoint]

def unscaleVec {M N : Nat} (scale : ℝ) (z : BlockVec M N) : BlockVec M N :=
  scale⁻¹ • z

theorem scaleVec_unscaleVec {M N : Nat} {scale : ℝ} (hs : scale ≠ 0)
    (z : BlockVec M N) : scaleVec scale (unscaleVec scale z) = z := by
  ext m j
  simp [scaleVec, unscaleVec, hs]

/-- A base proximal point transports to the scaled objective with coefficient
`amp * scale²`. -/
theorem IsHalfProxPoint.scaled {M N : Nat} {amp scale : ℝ}
    {f : BlockVec M N → ℝ} {xbar zbar : BlockVec M N}
    (hamp : 0 ≤ amp) (hs : scale ≠ 0)
    (hz : IsHalfProxPoint f xbar zbar)
    (x : BlockVec M N) (hx : xbar = scaleVec scale x) :
    IsRhoProxPoint (amp * scale ^ 2) (scaledFunction amp scale f) x
      (unscaleVec scale zbar) := by
  intro y
  have hbase := hz (scaleVec scale y)
  have hscaled := mul_le_mul_of_nonneg_left hbase hamp
  have hzscale : scaleVec scale (unscaleVec scale zbar) = zbar :=
    scaleVec_unscaleVec hs zbar
  have hzx :
      scaleVec scale (unscaleVec scale zbar - x) = zbar - xbar := by
    rw [← scaleVec_sub, hzscale, hx]
  have hyx : scaleVec scale (y - x) = scaleVec scale y - xbar := by
    rw [← scaleVec_sub, hx]
  have hsqz := blockSq_scaleVec scale (unscaleVec scale zbar - x)
  have hsqy := blockSq_scaleVec scale (y - x)
  rw [hzx] at hsqz
  rw [hyx] at hsqy
  unfold scaledFunction
  rw [hzscale]
  nlinarith

def rhoResidual {M N : Nat} (rho : ℝ)
    (x z : BlockVec M N) : BlockVec M N :=
  (2 * rho) • (x - z)

/-- Exact Moreau-residual scaling. -/
theorem rhoResidual_scaled {M N : Nat} (amp scale : ℝ)
    (x zbar : BlockVec M N) :
    rhoResidual (amp * scale ^ 2) x (unscaleVec scale zbar) =
      (amp * scale) • halfProxResidual (scaleVec scale x) zbar := by
  by_cases hs : scale = 0
  · subst scale
    simp [rhoResidual, halfProxResidual, scaleVec, unscaleVec]
  · ext m j
    simp [rhoResidual, halfProxResidual, scaleVec, unscaleVec]
    field_simp [hs]

/-- The paper's concrete coefficients simplify exactly. -/
theorem paper_scaling_coefficients {G rho : ℝ} (hG : G ≠ 0) (hrho : rho ≠ 0) :
    (G ^ 2 / rho) * (rho / G) = G ∧
    (G ^ 2 / rho) * (rho / G) ^ 2 = rho := by
  constructor <;> field_simp

end

end WeaklyConvexLowerBound

