import Mathlib

/-!
# Finite-dimensional Euclidean support

This module contains only the elementary finite-vector and Fréchet-derivative
infrastructure needed by the weakly convex lower-bound development.
-/

namespace WeaklyConvexLowerBound.Foundation

noncomputable section

open scoped BigOperators

/-- A finite real coordinate vector. -/
abbrev EVec (n : Nat) := Fin n → ℝ

/-- Squared Euclidean norm written as an explicit finite sum. -/
def vecSq {n : Nat} (x : EVec n) : ℝ :=
  ∑ i : Fin n, x i ^ 2

theorem vecSq_nonneg {n : Nat} (x : EVec n) : 0 ≤ vecSq x := by
  unfold vecSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Coordinatewise scalar multiplication. -/
def scaleEVec {n : Nat} (c : ℝ) (x : EVec n) : EVec n :=
  fun i => c * x i

theorem vecSq_scaleEVec {n : Nat} (c : ℝ) (x : EVec n) :
    vecSq (scaleEVec c x) = c ^ 2 * vecSq x := by
  unfold vecSq scaleEVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `HasFDerivAt` with the norm-induced topology on a finite Pi space made
explicit, avoiding an irrelevant topology-instance diamond. -/
def HasEVecFDerivAt {n : Nat} (f : EVec n → ℝ)
    (f' : EVec n →L[ℝ] ℝ) (x : EVec n) : Prop :=
  @HasFDerivAt ℝ _ (EVec n)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' x

/-- Differentiability with the same explicit finite-dimensional topology. -/
def EVecDifferentiableAt {n : Nat} (f : EVec n → ℝ) (x : EVec n) : Prop :=
  @DifferentiableAt ℝ _ (EVec n)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f x

/-- Continuous coordinate projection. -/
def evecProj {n : Nat} (i : Fin n) : EVec n →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec n) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec n) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec n) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun x : EVec n => x i
       map_add' := by intro x y; rfl
       map_smul' := by intro c x; rfl } : EVec n →ₗ[ℝ] ℝ)

@[simp] theorem evecProj_apply {n : Nat} (i : Fin n) (x : EVec n) :
    evecProj i x = x i := by
  unfold evecProj
  rfl

theorem continuousLinearMap_sum_apply {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
    [NormedSpace ℝ F] (f : ι → E →L[ℝ] F) (x : E) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Continuous linear functional represented by Euclidean dot product. -/
def evecDot {n : Nat} (g : EVec n) : EVec n →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec n) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec n) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec n) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h : EVec n => ∑ i : Fin n, g i * h i
       map_add' := by
         intro x y
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro i _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c x
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         ring } : EVec n →ₗ[ℝ] ℝ)

@[simp] theorem evecDot_apply {n : Nat} (g h : EVec n) :
    evecDot g h = ∑ i : Fin n, g i * h i := by
  unfold evecDot
  rfl

end

end WeaklyConvexLowerBound.Foundation
