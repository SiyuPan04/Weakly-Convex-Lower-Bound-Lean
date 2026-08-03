import WeaklyConvexLowerBound.Progress
import WeaklyConvexLowerBound.Foundation.Differentiability

/-!
# Fréchet derivative of the block progress carrier

`Progress` proves all numerical bounds for the vector called `psiGrad` in
the manuscript.  This file additionally verifies that this vector really
represents the Fréchet derivative of `psi`, including the two splice points
of the scalar smoothstep.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- Continuous linear functional represented by the displayed progress
gradient. -/
def psiGradientCLM {N : Nat} (u : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] ℝ :=
  WeaklyConvexLowerBound.Foundation.evecDot (psiGrad u)

/-- The displayed vector `psiGrad u` is the genuine Fréchet gradient of
`psi` at `u`. -/
theorem hasEVecFDerivAt_psi {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) :
    WeaklyConvexLowerBound.Foundation.HasEVecFDerivAt psi (psiGradientCLM u) u := by
  letI : AddCommGroup (Fin N → ℝ) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (Fin N → ℝ) := Pi.normedSpace.toModule
  letI : TopologicalSpace (Fin N → ℝ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold WeaklyConvexLowerBound.Foundation.HasEVecFDerivAt
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let D : Fin N → ((Fin N → ℝ) →L[ℝ] ℝ) := fun j =>
    (1 / (N : ℝ)) •
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (qPrime (((N : ℝ) / 4) * u j))).comp
          (((N : ℝ) / 4) • WeaklyConvexLowerBound.Foundation.evecProj j))
  have hsummand (j : Fin N) :
      HasFDerivAt
        (fun y : Fin N → ℝ =>
          (1 / (N : ℝ)) *
            (q ∘ fun v : Fin N → ℝ => ((N : ℝ) / 4) * v j) y)
        (D j) u := by
    have hcoord : HasFDerivAt (fun v : Fin N → ℝ => v j)
        (WeaklyConvexLowerBound.Foundation.evecProj j) u :=
      (WeaklyConvexLowerBound.Foundation.evecProj j).hasFDerivAt
    have hscaled := hcoord.const_mul ((N : ℝ) / 4)
    have hq := (hasDerivAt_q (((N : ℝ) / 4) * u j)).hasFDerivAt.comp u hscaled
    have hdiv := hq.const_mul (1 / (N : ℝ))
    simpa only [D] using hdiv
  have hsum :
      HasFDerivAt
        (fun v : Fin N → ℝ =>
          ∑ j : Fin N,
            (1 / (N : ℝ)) *
              (q ∘ fun w : Fin N → ℝ => ((N : ℝ) / 4) * w j) v)
        (∑ j : Fin N, D j) u := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact hsummand j
  have hfun :
      (fun v : Fin N → ℝ =>
        ∑ j : Fin N,
          (1 / (N : ℝ)) *
            (q ∘ fun w : Fin N → ℝ => ((N : ℝ) / 4) * w j) v) = psi := by
    funext v
    unfold psi
    rw [← Finset.mul_sum]
    have hargs :
        (∑ j : Fin N, (q ∘ fun w : Fin N → ℝ =>
          ((N : ℝ) / 4) * w j) v) =
          ∑ j : Fin N, q ((N : ℝ) * v j / 4) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg q (by ring)
    rw [hargs]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have hmap :
      (∑ j : Fin N, D j) = psiGradientCLM u := by
    apply ContinuousLinearMap.ext
    intro v
    rw [WeaklyConvexLowerBound.Foundation.continuousLinearMap_sum_apply]
    simp only [D, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      WeaklyConvexLowerBound.Foundation.evecProj_apply, psiGradientCLM,
      WeaklyConvexLowerBound.Foundation.evecDot_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    unfold psiGrad
    have harg : (N : ℝ) / 4 * u j = (N : ℝ) * u j / 4 := by ring
    rw [harg]
    field_simp [hNreal]
  rw [hfun, hmap] at hsum
  exact hsum

/-- Consequently `psi` is Fréchet differentiable everywhere (for the
positive block sizes used in the construction). -/
theorem eVecDifferentiableAt_psi {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) :
    WeaklyConvexLowerBound.Foundation.EVecDifferentiableAt psi u :=
  (hasEVecFDerivAt_psi hN u).differentiableAt

end

end WeaklyConvexLowerBound


