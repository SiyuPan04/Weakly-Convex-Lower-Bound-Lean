import WeaklyConvexLowerBound.Rotation
import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Exact invariance under an orthonormal hidden frame

This file records the invariance statements needed by the resisting-oracle
reduction.  All norms and inner products are the explicit Euclidean sums used
in the manuscript, rather than the sup norm carried by a finite Pi type.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-! ## Ambient regularity predicates -/

/-- Squared-norm Euclidean Lipschitz continuity in the ambient space. -/
def EVectorEuclideanLipschitz {D : Nat} (C : ℝ)
    (f : EVector D → ℝ) : Prop :=
  ∀ X Y, (f X - f Y) ^ 2 ≤
    C ^ 2 * WeaklyConvexLowerBound.Foundation.vecSq (X - Y)

/-- Weak convexity in the ambient Euclidean space. -/
def EVectorWeaklyConvex {D : Nat} (ρ : ℝ)
    (f : EVector D → ℝ) : Prop :=
  ConvexOn ℝ Set.univ
    (fun X => f X + ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq X)

theorem euclideanLipschitz_rotate {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {C : ℝ} {f : BlockVec M N → ℝ}
    (hf : EuclideanLipschitz C f) :
    EVectorEuclideanLipschitz C (rotatedValue f U) := by
  intro X Y
  have hbase := hf (blockProject U X) (blockProject U Y)
  have hproj :
      blockSq (blockProject U X - blockProject U Y) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (X - Y) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  unfold rotatedValue
  have hC : 0 ≤ C ^ 2 := sq_nonneg C
  exact hbase.trans (mul_le_mul_of_nonneg_left hproj hC)

theorem blockProject_smul {M N D : Nat}
    (U : Fin (M * N) → EVector D) (a : ℝ) (X : EVector D) :
    blockProject U (a • X) = a • blockProject U X := by
  ext m j
  unfold blockProject unflatten WeaklyConvexLowerBound.Foundation.frameProject
  unfold WeaklyConvexLowerBound.Foundation.evecDotValue
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem blockEmbed_smul {M N D : Nat}
    (U : Fin (M * N) → EVector D) (a : ℝ) (z : BlockVec M N) :
    blockEmbed U (a • z) = a • blockEmbed U z := by
  ext k
  unfold blockEmbed WeaklyConvexLowerBound.Foundation.frameEmbed flatten
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem blockProject_combo {M N D : Nat}
    (U : Fin (M * N) → EVector D) (a b : ℝ) (X Y : EVector D) :
    blockProject U (a • X + b • Y) =
      a • blockProject U X + b • blockProject U Y := by
  rw [blockProject_add, blockProject_smul, blockProject_smul]

/-- Component perpendicular to the hidden frame. -/
def orthogonalResidual {M N D : Nat}
    (U : Fin (M * N) → EVector D) (X : EVector D) : EVector D :=
  X - blockEmbed U (blockProject U X)

theorem blockProject_orthogonalResidual {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (X : EVector D) :
    blockProject U (orthogonalResidual U X) = 0 := by
  unfold orthogonalResidual
  rw [blockProject_sub, blockProject_blockEmbed hU]
  exact sub_self _

theorem orthogonalResidual_combo {M N D : Nat}
    (U : Fin (M * N) → EVector D) (a b : ℝ) (X Y : EVector D) :
    orthogonalResidual U (a • X + b • Y) =
      a • orthogonalResidual U X + b • orthogonalResidual U Y := by
  unfold orthogonalResidual
  rw [blockProject_combo, blockEmbed_add, blockEmbed_smul, blockEmbed_smul]
  module

theorem evecDotValue_blockEmbed_project {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (X : EVector D) :
    WeaklyConvexLowerBound.Foundation.evecDotValue
        (blockEmbed U (blockProject U X)) X =
      blockSq (blockProject U X) := by
  unfold blockEmbed blockProject
  simp only [flatten_unflatten]
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_frameEmbed_project hU,
    ← vecSq_flatten]
  simp only [flatten_unflatten]

/-- Pythagoras for the hidden-frame projection and its perpendicular
residual, stated in the explicit squared norms used by the paper. -/
theorem vecSq_orthogonal_decomposition {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (X : EVector D) :
    WeaklyConvexLowerBound.Foundation.vecSq X =
      blockSq (blockProject U X) +
        WeaklyConvexLowerBound.Foundation.vecSq (orthogonalResidual U X) := by
  have hsub := WeaklyConvexLowerBound.Foundation.vecSq_sub_expand X
    (blockEmbed U (blockProject U X))
  rw [← WeaklyConvexLowerBound.Foundation.evecDotValue_comm,
    evecDotValue_blockEmbed_project hU,
    blockSq_blockEmbed hU] at hsub
  unfold orthogonalResidual
  nlinarith

theorem evecSq_convex_combo {D : Nat} (X Y : EVector D)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    WeaklyConvexLowerBound.Foundation.vecSq (a • X + b • Y) ≤
      a * WeaklyConvexLowerBound.Foundation.vecSq X + b * WeaklyConvexLowerBound.Foundation.vecSq Y := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  calc
    (∑ k, (a • X + b • Y) k ^ 2) ≤
        ∑ k, (a * X k ^ 2 + b * Y k ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hab0 : 0 ≤ a * b := mul_nonneg ha hb
      nlinarith [mul_nonneg hab0 (sq_nonneg (X k - Y k))]
    _ = a * (∑ k, X k ^ 2) + b * (∑ k, Y k ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem weaklyConvex_rotate {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {f : BlockVec M N → ℝ}
    (hf : WeaklyConvex ρ f) :
    EVectorWeaklyConvex ρ (rotatedValue f U) := by
  refine ⟨convex_univ, ?_⟩
  intro X _ Y _ a b ha hb hab
  have hbase := hf.2 (Set.mem_univ (blockProject U X))
    (Set.mem_univ (blockProject U Y)) ha hb hab
  have hres := evecSq_convex_combo
    (orthogonalResidual U X) (orthogonalResidual U Y) a b ha hb hab
  have hresScaled := mul_le_mul_of_nonneg_left hres (by
    exact div_nonneg hρ (by norm_num : (0 : ℝ) ≤ 2))
  have hdecX := vecSq_orthogonal_decomposition hU X
  have hdecY := vecSq_orthogonal_decomposition hU Y
  have hdecMix := vecSq_orthogonal_decomposition hU (a • X + b • Y)
  rw [orthogonalResidual_combo] at hdecMix
  rw [blockProject_combo] at hdecMix
  change
    f (blockProject U (a • X + b • Y)) +
        ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq (a • X + b • Y) ≤
      a • (f (blockProject U X) + ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq X) +
        b • (f (blockProject U Y) + ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq Y)
  simp only [smul_eq_mul]
  rw [blockProject_combo]
  change
    f (a • blockProject U X + b • blockProject U Y) +
        ρ / 2 * blockSq (a • blockProject U X + b • blockProject U Y) ≤
      a * (f (blockProject U X) + ρ / 2 * blockSq (blockProject U X)) +
        b * (f (blockProject U Y) + ρ / 2 * blockSq (blockProject U Y))
    at hbase
  calc
    f (a • blockProject U X + b • blockProject U Y) +
          ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq (a • X + b • Y) =
        (f (a • blockProject U X + b • blockProject U Y) +
          ρ / 2 * blockSq (a • blockProject U X + b • blockProject U Y)) +
          ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq
            (a • orthogonalResidual U X + b • orthogonalResidual U Y) := by
              rw [hdecMix]
              ring
    _ ≤ (a * (f (blockProject U X) +
              ρ / 2 * blockSq (blockProject U X)) +
            b * (f (blockProject U Y) +
              ρ / 2 * blockSq (blockProject U Y))) +
          ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq
            (a • orthogonalResidual U X + b • orthogonalResidual U Y) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hbase
            (ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq
              (a • orthogonalResidual U X + b • orthogonalResidual U Y))
    _ ≤ (a * (f (blockProject U X) +
              ρ / 2 * blockSq (blockProject U X)) +
            b * (f (blockProject U Y) +
              ρ / 2 * blockSq (blockProject U Y))) +
          ρ / 2 * (a * WeaklyConvexLowerBound.Foundation.vecSq (orthogonalResidual U X) +
            b * WeaklyConvexLowerBound.Foundation.vecSq (orthogonalResidual U Y)) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hresScaled
            (a * (f (blockProject U X) +
                ρ / 2 * blockSq (blockProject U X)) +
              b * (f (blockProject U Y) +
                ρ / 2 * blockSq (blockProject U Y)))
    _ = a * (f (blockProject U X) +
            ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq X) +
          b * (f (blockProject U Y) +
            ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq Y) := by
      rw [hdecX, hdecY]
      ring

/-! ## Exact covariance of quadratic-support subgradients -/

theorem evecDotValue_blockEmbed_left {M N D : Nat}
    (U : Fin (M * N) → EVector D) (g : BlockVec M N) (V : EVector D) :
    WeaklyConvexLowerBound.Foundation.evecDotValue (blockEmbed U g) V =
      blockDot g (blockProject U V) := by
  unfold blockEmbed blockProject
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_frameEmbed_left]
  rw [← evecDotValue_flatten]
  simp only [flatten_unflatten]
  rfl

theorem evecDotValue_blockEmbed_right {M N D : Nat}
    (U : Fin (M * N) → EVector D) (G : EVector D) (v : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.evecDotValue G (blockEmbed U v) =
      blockDot (blockProject U G) v := by
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm,
    evecDotValue_blockEmbed_left]
  exact blockDot_comm v (blockProject U G)

theorem vecSq_smul {D : Nat} (a : ℝ) (X : EVector D) :
    WeaklyConvexLowerBound.Foundation.vecSq (a • X) = a ^ 2 * WeaklyConvexLowerBound.Foundation.vecSq X := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem evecDotValue_smul_right {D : Nat} (G V : EVector D) (a : ℝ) :
    WeaklyConvexLowerBound.Foundation.evecDotValue G (a • V) =
      a * WeaklyConvexLowerBound.Foundation.evecDotValue G V := by
  rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm,
    WeaklyConvexLowerBound.Foundation.evecDotValue_smul_left,
    WeaklyConvexLowerBound.Foundation.evecDotValue_comm]

theorem evecDotValue_sub_right {D : Nat} (G V W : EVector D) :
    WeaklyConvexLowerBound.Foundation.evecDotValue G (V - W) =
      WeaklyConvexLowerBound.Foundation.evecDotValue G V -
        WeaklyConvexLowerBound.Foundation.evecDotValue G W := by
  unfold WeaklyConvexLowerBound.Foundation.evecDotValue
  simp only [Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- A block quadratic support lifts at every ambient representative of the
same projected point, not only at the canonical embedded representative. -/
theorem qSubgradient_rotate_at {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {c : ℝ} (hc : 0 ≤ c) {f : BlockVec M N → ℝ}
    {X : EVector D} {g : BlockVec M N}
    (hg : QSubgradient c f (blockProject U X) g) :
    EVectorQSubgradient c (rotatedValue f U) X (blockEmbed U g) := by
  intro Y
  have hbase := hg (blockProject U Y)
  have hdot :
      WeaklyConvexLowerBound.Foundation.evecDotValue (blockEmbed U g) (Y - X) =
        blockDot g (blockProject U Y - blockProject U X) := by
    rw [evecDotValue_blockEmbed_left, ← blockProject_sub]
  have hnorm :
      blockSq (blockProject U Y - blockProject U X) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (Y - X) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  unfold rotatedValue
  rw [hdot]
  nlinarith

/-- Projecting an ambient quadratic support yields a block quadratic
support.  The proof tests only ambient points with the same perpendicular
component as the base point. -/
theorem eVectorQSubgradient_project {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {c : ℝ} {f : BlockVec M N → ℝ}
    {X G : EVector D}
    (hG : EVectorQSubgradient c (rotatedValue f U) X G) :
    QSubgradient c f (blockProject U X) (blockProject U G) := by
  intro y
  let Y := ambientProxLift U X y
  have hsupp := hG Y
  have hPY : blockProject U Y = y :=
    blockProject_ambientProxLift hU X y
  have hdiff : Y - X = blockEmbed U (y - blockProject U X) :=
    ambientProxLift_sub U X y
  have hdot :
      WeaklyConvexLowerBound.Foundation.evecDotValue G (Y - X) =
        blockDot (blockProject U G) (y - blockProject U X) := by
    rw [hdiff, evecDotValue_blockEmbed_right]
  have hnorm : WeaklyConvexLowerBound.Foundation.vecSq (Y - X) =
      blockSq (y - blockProject U X) :=
    vecSq_ambientProxLift_sub hU X y
  unfold rotatedValue at hsupp
  rw [hPY, hdot, hnorm] at hsupp
  exact hsupp

theorem evecDotValue_orthogonalResidual_self {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (G : EVector D) :
    WeaklyConvexLowerBound.Foundation.evecDotValue G (orthogonalResidual U G) =
      WeaklyConvexLowerBound.Foundation.vecSq (orthogonalResidual U G) := by
  have hdot :
      WeaklyConvexLowerBound.Foundation.evecDotValue G
          (blockEmbed U (blockProject U G)) =
        blockSq (blockProject U G) := by
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_comm]
    exact evecDotValue_blockEmbed_project hU G
  have hdec := vecSq_orthogonal_decomposition hU G
  unfold orthogonalResidual at hdec ⊢
  rw [evecDotValue_sub_right,
    WeaklyConvexLowerBound.Foundation.evecDotValue_self, hdot]
  linarith

theorem evec_eq_zero_of_vecSq_eq_zero {D : Nat} (V : EVector D)
    (hV : WeaklyConvexLowerBound.Foundation.vecSq V = 0) : V = 0 := by
  funext k
  have hk : V k ^ 2 ≤ ∑ i, V i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (V i))
      (Finset.mem_univ k)
  unfold WeaklyConvexLowerBound.Foundation.vecSq at hV
  rw [hV] at hk
  have : V k = 0 := by nlinarith [sq_nonneg (V k)]
  simpa using this

/-- An ambient quadratic support of a function that is constant in the
orthogonal complement cannot contain any orthogonal subgradient component.
The positive test scale `1/(c+1)` works uniformly also at `c = 0`. -/
theorem eVectorQSubgradient_eq_blockEmbed_project {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {c : ℝ} (hc : 0 ≤ c) {f : BlockVec M N → ℝ}
    {X G : EVector D}
    (hG : EVectorQSubgradient c (rotatedValue f U) X G) :
    G = blockEmbed U (blockProject U G) := by
  let R : EVector D := orthogonalResidual U G
  let t : ℝ := 1 / (c + 1)
  have hden : 0 < c + 1 := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact one_div_pos.mpr hden
  have hcoef : 0 < t - c * t ^ 2 := by
    have hden0 : c + 1 ≠ 0 := ne_of_gt hden
    dsimp [t]
    rw [show 1 / (c + 1) - c * (1 / (c + 1)) ^ 2 =
        1 / (c + 1) ^ 2 by
      field_simp [hden0]
      ring]
    positivity
  let Y : EVector D := X + t • R
  have hPR : blockProject U R = 0 := by
    dsimp [R]
    exact blockProject_orthogonalResidual hU G
  have hPY : blockProject U Y = blockProject U X := by
    dsimp [Y]
    rw [blockProject_add, blockProject_smul, hPR]
    simp
  have hdiff : Y - X = t • R := by
    dsimp [Y]
    module
  have hsupp := hG Y
  unfold rotatedValue at hsupp
  rw [hPY, hdiff, evecDotValue_smul_right, vecSq_smul] at hsupp
  have hdotR : WeaklyConvexLowerBound.Foundation.evecDotValue G R =
      WeaklyConvexLowerBound.Foundation.vecSq R := by
    dsimp [R]
    exact evecDotValue_orthogonalResidual_self hU G
  rw [hdotR] at hsupp
  have hRnonneg : 0 ≤ WeaklyConvexLowerBound.Foundation.vecSq R := by
    unfold WeaklyConvexLowerBound.Foundation.vecSq
    positivity
  have hprod :
      (t - c * t ^ 2) * WeaklyConvexLowerBound.Foundation.vecSq R ≤ 0 := by
    nlinarith
  have hprodNonneg :
      0 ≤ (t - c * t ^ 2) * WeaklyConvexLowerBound.Foundation.vecSq R :=
    mul_nonneg hcoef.le hRnonneg
  have hprodZero :
      (t - c * t ^ 2) * WeaklyConvexLowerBound.Foundation.vecSq R = 0 :=
    le_antisymm hprod hprodNonneg
  have hRsq : WeaklyConvexLowerBound.Foundation.vecSq R = 0 := by
    rcases mul_eq_zero.mp hprodZero with hbad | hzero
    · exact False.elim (ne_of_gt hcoef hbad)
    · exact hzero
  have hRzero : R = 0 := evec_eq_zero_of_vecSq_eq_zero R hRsq
  dsimp [R, orthogonalResidual] at hRzero
  exact sub_eq_zero.mp hRzero

/-- Exact set identity for the quadratic-support oracle under rotation. -/
theorem eVectorQSubdiff_rotate_eq {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {c : ℝ} (hc : 0 ≤ c) (f : BlockVec M N → ℝ) (X : EVector D) :
    {G | EVectorQSubgradient c (rotatedValue f U) X G} =
      blockEmbed U '' qSubdiff c f (blockProject U X) := by
  ext G
  constructor
  · intro hG
    refine ⟨blockProject U G, ?_, ?_⟩
    · exact eVectorQSubgradient_project hU hG
    · exact (eVectorQSubgradient_eq_blockEmbed_project hU hc hG).symm
  · rintro ⟨g, hg, rfl⟩
    exact qSubgradient_rotate_at hU hc hg

/-! ## Exact covariance of the semantic full subdifferential -/

/-- Ambient quadratic convexification. -/
def EVectorConvexification {D : Nat} (ρ : ℝ) (f : EVector D → ℝ) :
    EVector D → ℝ :=
  fun X => f X + ρ / 2 * WeaklyConvexLowerBound.Foundation.vecSq X

/-- Global support subgradient of an ambient convex finite-valued function. -/
def EVectorConvexSubgradient {D : Nat} (h : EVector D → ℝ)
    (X P : EVector D) : Prop :=
  ∀ Y, h X + WeaklyConvexLowerBound.Foundation.evecDotValue P (Y - X) ≤ h Y

/-- Full weakly-convex subgradient obtained by translating the convex
subgradient of the quadratic convexification. -/
def EVectorFullSubgradient {D : Nat} (ρ : ℝ) (f : EVector D → ℝ)
    (X G : EVector D) : Prop :=
  EVectorConvexSubgradient (EVectorConvexification ρ f) X (G + ρ • X)

def eVectorFullSubdiff {D : Nat} (ρ : ℝ) (f : EVector D → ℝ)
    (X : EVector D) : Set (EVector D) :=
  {G | EVectorFullSubgradient ρ f X G}

theorem evecSq_eq_at_add_displacement {D : Nat} (Y X : EVector D) :
    WeaklyConvexLowerBound.Foundation.vecSq Y =
      WeaklyConvexLowerBound.Foundation.vecSq X +
        2 * WeaklyConvexLowerBound.Foundation.evecDotValue X (Y - X) +
          WeaklyConvexLowerBound.Foundation.vecSq (Y - X) := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq WeaklyConvexLowerBound.Foundation.evecDotValue
  calc
    (∑ k, Y k ^ 2) =
        ∑ k, (X k ^ 2 + 2 * (X k * (Y - X) k) + (Y - X) k ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Pi.sub_apply]
      ring
    _ = (∑ k, X k ^ 2) + 2 * (∑ k, X k * (Y - X) k) +
          ∑ k, (Y - X) k ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The ambient full subdifferential is exactly the ambient global
quadratic-support relation. -/
theorem eVectorFullSubgradient_iff_qSubgradient {D : Nat}
    (ρ : ℝ) (f : EVector D → ℝ) (X G : EVector D) :
    EVectorFullSubgradient ρ f X G ↔
      EVectorQSubgradient (ρ / 2) f X G := by
  constructor
  · intro hG Y
    have h := hG Y
    unfold EVectorConvexSubgradient EVectorConvexification at h
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_add_left,
      WeaklyConvexLowerBound.Foundation.evecDotValue_smul_left,
      evecSq_eq_at_add_displacement Y X] at h
    nlinarith
  · intro hG Y
    have h := hG Y
    unfold EVectorConvexification
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_add_left,
      WeaklyConvexLowerBound.Foundation.evecDotValue_smul_left,
      evecSq_eq_at_add_displacement Y X]
    nlinarith

theorem mem_eVectorFullSubdiff_iff_qSubgradient {D : Nat}
    (ρ : ℝ) (f : EVector D → ℝ) (X G : EVector D) :
    G ∈ eVectorFullSubdiff ρ f X ↔
      EVectorQSubgradient (ρ / 2) f X G := by
  exact eVectorFullSubgradient_iff_qSubgradient ρ f X G

/-- The manuscript's exact full-subdifferential rotation rule.  Every
ambient full subgradient is an embedded block full subgradient and every
embedded block full subgradient occurs; no inclusion is lost. -/
theorem eVectorFullSubdiff_rotate_eq {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BlockVec M N → ℝ) (X : EVector D) :
    eVectorFullSubdiff ρ (rotatedValue f U) X =
      blockEmbed U '' fullSubdiff ρ f (blockProject U X) := by
  ext G
  constructor
  · intro hG
    have hq : EVectorQSubgradient (ρ / 2) (rotatedValue f U) X G :=
      (mem_eVectorFullSubdiff_iff_qSubgradient ρ _ X G).mp hG
    refine ⟨blockProject U G, ?_, ?_⟩
    · exact (mem_fullSubdiff_iff_qSubgradient ρ f _ _).mpr
        (eVectorQSubgradient_project hU hq)
    · exact (eVectorQSubgradient_eq_blockEmbed_project hU
        (div_nonneg hρ (by norm_num)) hq).symm
  · rintro ⟨g, hg, rfl⟩
    apply (mem_eVectorFullSubdiff_iff_qSubgradient ρ _ X _).mpr
    apply qSubgradient_rotate_at hU (div_nonneg hρ (by norm_num))
    exact (mem_fullSubdiff_iff_qSubgradient ρ f _ _).mp hg

/-! ## Proximal residuals and stationarity thresholds -/

/-- Ambient Moreau residual in the same normalization as
`halfProxResidual`, namely `2 (Y - Z)`. -/
def eVectorHalfProxResidual {D : Nat} (Y Z : EVector D) : EVector D :=
  (2 : ℝ) • (Y - Z)

theorem eVectorHalfProxResidual_ambientProxLift {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (_hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (Y : EVector D) (z : BlockVec M N) :
    eVectorHalfProxResidual Y (ambientProxLift U Y z) =
      blockEmbed U (halfProxResidual (blockProject U Y) z) := by
  have hsub : Y - ambientProxLift U Y z =
      blockEmbed U (blockProject U Y - z) := by
    unfold ambientProxLift
    calc
      Y - (Y + blockEmbed U (z - blockProject U Y)) =
          -blockEmbed U (z - blockProject U Y) := by module
      _ = blockEmbed U (-(z - blockProject U Y)) := by
        rw [show -blockEmbed U (z - blockProject U Y) =
          (-1 : ℝ) • blockEmbed U (z - blockProject U Y) by simp,
          ← blockEmbed_smul]
        congr 1
        simp
      _ = blockEmbed U (blockProject U Y - z) := by
        congr 1
        module
  unfold eVectorHalfProxResidual halfProxResidual
  rw [hsub, ← blockEmbed_smul]

theorem vecSq_eVectorHalfProxResidual_ambientProxLift {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (Y : EVector D) (z : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.vecSq
        (eVectorHalfProxResidual Y (ambientProxLift U Y z)) =
      blockSq (halfProxResidual (blockProject U Y) z) := by
  rw [eVectorHalfProxResidual_ambientProxLift hU,
    blockSq_blockEmbed hU]

theorem norm_eVectorHalfProxResidual_ambientProxLift {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (Y : EVector D) (z : BlockVec M N) :
    Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq
        (eVectorHalfProxResidual Y (ambientProxLift U Y z))) =
      Real.sqrt (blockSq (halfProxResidual (blockProject U Y) z)) := by
  rw [vecSq_eVectorHalfProxResidual_ambientProxLift hU]

/-- Exact correspondence for a chosen block proximal point and its canonical
ambient lift. -/
theorem halfProxPoint_rotate_iff {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) (Y : EVector D) (z : BlockVec M N) :
    EVectorIsHalfProxPoint (rotatedValue f U) Y
        (ambientProxLift U Y z) ↔
      IsHalfProxPoint f (blockProject U Y) z := by
  constructor
  · intro hZ
    have hp := EVectorIsHalfProxPoint.project hU hZ
    rw [blockProject_ambientProxLift hU] at hp
    exact hp
  · exact IsHalfProxPoint.rotate hU

theorem blockProject_eVectorHalfProxResidual {M N D : Nat}
    (U : Fin (M * N) → EVector D) (Y Z : EVector D) :
    blockProject U (eVectorHalfProxResidual Y Z) =
      halfProxResidual (blockProject U Y) (blockProject U Z) := by
  unfold eVectorHalfProxResidual halfProxResidual
  rw [blockProject_smul, blockProject_sub]

theorem blockSq_halfProxResidual_project_le {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (Y Z : EVector D) :
    blockSq (halfProxResidual (blockProject U Y) (blockProject U Z)) ≤
      WeaklyConvexLowerBound.Foundation.vecSq (eVectorHalfProxResidual Y Z) := by
  rw [← blockProject_eVectorHalfProxResidual]
  exact blockSq_blockProject_le hU _

/-- Existence of a block proximal point with residual squared norm at most
`τ`.  This threshold form is exactly what the stationarity hitting test uses. -/
def HalfProxStationaritySqLe {M N : Nat} (f : BlockVec M N → ℝ)
    (y : BlockVec M N) (τ : ℝ) : Prop :=
  ∃ z, IsHalfProxPoint f y z ∧ blockSq (halfProxResidual y z) ≤ τ

/-- Ambient counterpart of `HalfProxStationaritySqLe`. -/
def EVectorHalfProxStationaritySqLe {D : Nat} (f : EVector D → ℝ)
    (Y : EVector D) (τ : ℝ) : Prop :=
  ∃ Z, EVectorIsHalfProxPoint f Y Z ∧
    WeaklyConvexLowerBound.Foundation.vecSq (eVectorHalfProxResidual Y Z) ≤ τ

/-- Exact preservation of every proximal-stationarity threshold.  The
forward direction uses the isometric lift; the reverse direction projects an
arbitrary ambient proximal point and uses orthogonal contraction. -/
theorem halfProxStationaritySqLe_rotate_iff {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) (Y : EVector D) (τ : ℝ) :
    EVectorHalfProxStationaritySqLe (rotatedValue f U) Y τ ↔
      HalfProxStationaritySqLe f (blockProject U Y) τ := by
  constructor
  · rintro ⟨Z, hZ, hsmall⟩
    refine ⟨blockProject U Z, EVectorIsHalfProxPoint.project hU hZ, ?_⟩
    exact (blockSq_halfProxResidual_project_le hU Y Z).trans hsmall
  · rintro ⟨z, hz, hsmall⟩
    refine ⟨ambientProxLift U Y z, IsHalfProxPoint.rotate hU hz, ?_⟩
    rw [vecSq_eVectorHalfProxResidual_ambientProxLift hU]
    exact hsmall


/-! ## Value range and initial gap -/

theorem range_rotatedValue_eq {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) :
    Set.range (rotatedValue f U) = Set.range f := by
  ext r
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨blockProject U X, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨blockEmbed U z, ?_⟩
    simp [rotatedValue, blockProject_blockEmbed hU]

theorem sInf_range_rotatedValue_eq {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) :
    sInf (Set.range (rotatedValue f U)) = sInf (Set.range f) := by
  rw [range_rotatedValue_eq hU f]

theorem bddBelow_range_rotatedValue_iff {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) :
    BddBelow (Set.range (rotatedValue f U)) ↔ BddBelow (Set.range f) := by
  rw [range_rotatedValue_eq hU f]

theorem rotatedValue_zero {M N D : Nat}
    (U : Fin (M * N) → EVector D) (f : BlockVec M N → ℝ) :
    rotatedValue f U 0 = f 0 := by
  simp [rotatedValue]

theorem initialGap_rotate {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (f : BlockVec M N → ℝ) :
    rotatedValue f U 0 - sInf (Set.range (rotatedValue f U)) =
      f 0 - sInf (Set.range f) := by
  rw [rotatedValue_zero, sInf_range_rotatedValue_eq hU f]

end

end WeaklyConvexLowerBound

