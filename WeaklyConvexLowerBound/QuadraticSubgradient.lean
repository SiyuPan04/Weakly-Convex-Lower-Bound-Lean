import WeaklyConvexLowerBound.Basic

/-!
# Quadratic-support subgradients and proximal optimality

Mathlib does not currently provide Clarke/limiting subdifferentials.  For a
finite weakly convex function, the standard subdifferentials are equivalently
described by a global quadratic support inequality.  This file uses that
description directly.  It is also exactly what is needed in the terminal
Moreau-envelope argument.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- `g` supports `f` at `z` up to quadratic error `c * ‖x-z‖²`. -/
def QSubgradient {M N : Nat} (c : ℝ) (f : BlockVec M N → ℝ)
    (z g : BlockVec M N) : Prop :=
  ∀ x, f z + blockDot g (x - z) - c * blockSq (x - z) ≤ f x

/-- Quadratic-support subgradients form a set-valued full oracle reply. -/
def qSubdiff {M N : Nat} (c : ℝ) (f : BlockVec M N → ℝ)
    (z : BlockVec M N) : Set (BlockVec M N) :=
  {g | QSubgradient c f z g}

theorem QSubgradient.mono {M N : Nat} {a b : ℝ}
    {f : BlockVec M N → ℝ} {z g : BlockVec M N}
    (hab : a ≤ b) (hg : QSubgradient a f z g) :
    QSubgradient b f z g := by
  intro x
  have hs : 0 ≤ blockSq (x - z) := blockSq_nonneg _
  have h := hg x
  nlinarith

/-- The Euclidean three-point expansion used by proximal optimality. -/
theorem blockSq_three_point {M N : Nat} (x y z : BlockVec M N) :
    blockSq (x - y) = blockSq (x - z) + blockSq (z - y) +
      2 * blockDot (x - z) (z - y) := by
  unfold blockSq blockDot
  calc
    (∑ m, ∑ j, (x - y) m j ^ 2) =
        ∑ m, ∑ j, ((x - z) m j ^ 2 + (z - y) m j ^ 2 +
          2 * ((x - z) m j * (z - y) m j)) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.sub_apply]
      ring
    _ = (∑ m, ∑ j, (x - z) m j ^ 2) +
        (∑ m, ∑ j, (z - y) m j ^ 2) +
          2 * ∑ m, ∑ j, (x - z) m j * (z - y) m j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem blockDot_comm {M N : Nat} (x y : BlockVec M N) :
    blockDot x y = blockDot y x := by
  unfold blockDot
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem blockDot_smul_left {M N : Nat} (a : ℝ)
    (x y : BlockVec M N) : blockDot (a • x) y = a * blockDot x y := by
  unfold blockDot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `z` minimizes the paper's proximal objective
`x ↦ f x + ‖x-y‖²` (Moreau parameter `1/2`). -/
def IsHalfProxPoint {M N : Nat} (f : BlockVec M N → ℝ)
    (y z : BlockVec M N) : Prop :=
  ∀ x, f z + blockSq (z - y) ≤ f x + blockSq (x - y)

/-- The residual vector represented by the Moreau gradient at parameter
`1/2`, once a proximal point has been selected. -/
def halfProxResidual {M N : Nat} (y z : BlockVec M N) : BlockVec M N :=
  (2 : ℝ) • (y - z)

/-- Proximal minimality directly gives the quadratic-support Fermat
condition.  No nonsmooth-calculus axiom is used. -/
theorem IsHalfProxPoint.residual_qSubgradient {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) :
    QSubgradient 1 f z (halfProxResidual y z) := by
  intro x
  have hmin := hz x
  rw [blockSq_three_point x y z] at hmin
  have hdot :
      blockDot (halfProxResidual y z) (x - z) =
        -2 * blockDot (x - z) (z - y) := by
    unfold halfProxResidual
    rw [blockDot_smul_left, blockDot_comm (y - z) (x - z)]
    have hneg : y - z = -(z - y) := by
      ext m j
      simp
    rw [hneg]
    unfold blockDot
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring
  rw [hdot]
  linarith

/-- The residual belongs to the full quadratic-support set. -/
theorem IsHalfProxPoint.residual_mem_qSubdiff {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) :
    halfProxResidual y z ∈ qSubdiff 1 f z :=
  hz.residual_qSubgradient

end

end WeaklyConvexLowerBound

