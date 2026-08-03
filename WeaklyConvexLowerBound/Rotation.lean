import WeaklyConvexLowerBound.FullOracleModel
import WeaklyConvexLowerBound.QuadraticSubgradient
import WeaklyConvexLowerBound.Foundation.OrthonormalFrames

/-!
# Euclidean block serialization and orthogonal rotations

The paper first constructs a hard function on `M` blocks of length `N` and
then hides those `M*N` coordinates in an ambient Euclidean space.  This file
makes that identification and every norm/inner-product identity explicit.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- Serialize the block representation in the product order used by
`finProdFinEquiv`. -/
def flatten {M N : Nat} (z : BlockVec M N) : EVector (M * N) :=
  fun k =>
    let p := finProdFinEquiv.symm k
    z p.1 p.2

/-- Recover the block representation from a serialized Euclidean vector. -/
def unflatten {M N : Nat} (x : EVector (M * N)) : BlockVec M N :=
  fun m j => x (finProdFinEquiv (m, j))

@[simp] theorem unflatten_flatten {M N : Nat} (z : BlockVec M N) :
    unflatten (flatten z) = z := by
  funext m j
  simp [unflatten, flatten]

@[simp] theorem flatten_unflatten {M N : Nat} (x : EVector (M * N)) :
    flatten (unflatten x) = x := by
  funext k
  change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
  rw [Equiv.apply_symm_apply]

@[simp] theorem flatten_zero {M N : Nat} :
    flatten (0 : BlockVec M N) = 0 := by
  funext k
  simp [flatten]

@[simp] theorem unflatten_zero {M N : Nat} :
    unflatten (0 : EVector (M * N)) = 0 := by
  funext m j
  simp [unflatten]

theorem flatten_sub {M N : Nat} (x y : BlockVec M N) :
    flatten (x - y) = flatten x - flatten y := by
  funext k
  simp [flatten]

theorem unflatten_sub {M N : Nat} (x y : EVector (M * N)) :
    unflatten (x - y) = unflatten x - unflatten y := by
  funext m j
  simp [unflatten]

theorem flatten_add {M N : Nat} (x y : BlockVec M N) :
    flatten (x + y) = flatten x + flatten y := by
  funext k
  simp [flatten]

theorem unflatten_add {M N : Nat} (x y : EVector (M * N)) :
    unflatten (x + y) = unflatten x + unflatten y := by
  funext m j
  simp [unflatten]

theorem vecSq_flatten {M N : Nat} (z : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.vecSq (flatten z) = blockSq z := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq blockSq
  calc
    (∑ k : Fin (M * N), flatten z k ^ 2) =
        ∑ p : Fin M × Fin N, flatten z (finProdFinEquiv p) ^ 2 := by
      symm
      exact Equiv.sum_comp finProdFinEquiv
        (fun k : Fin (M * N) => flatten z k ^ 2)
    _ = ∑ p : Fin M × Fin N, z p.1 p.2 ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      simp [flatten]
    _ = ∑ m : Fin M, ∑ j : Fin N, z m j ^ 2 := by
      rw [Fintype.sum_prod_type]

theorem evecDotValue_flatten {M N : Nat} (x y : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.evecDotValue (flatten x) (flatten y) = blockDot x y := by
  unfold WeaklyConvexLowerBound.Foundation.evecDotValue blockDot
  calc
    (∑ k : Fin (M * N), flatten x k * flatten y k) =
        ∑ p : Fin M × Fin N,
          flatten x (finProdFinEquiv p) * flatten y (finProdFinEquiv p) := by
      symm
      exact Equiv.sum_comp finProdFinEquiv
        (fun k : Fin (M * N) => flatten x k * flatten y k)
    _ = ∑ p : Fin M × Fin N, x p.1 p.2 * y p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      simp [flatten]
    _ = ∑ m : Fin M, ∑ j : Fin N, x m j * y m j := by
      rw [Fintype.sum_prod_type]

/-- Projection from the ambient space into the hidden `M*N`-dimensional
block coordinate system. -/
def blockProject {M N D : Nat}
    (U : Fin (M * N) → EVector D) (X : EVector D) : BlockVec M N :=
  unflatten (WeaklyConvexLowerBound.Foundation.frameProject U X)

/-- Embed a block vector into the ambient frame. -/
def blockEmbed {M N D : Nat}
    (U : Fin (M * N) → EVector D) (z : BlockVec M N) : EVector D :=
  WeaklyConvexLowerBound.Foundation.frameEmbed U (flatten z)

@[simp] theorem blockProject_zero {M N D : Nat}
    (U : Fin (M * N) → EVector D) : blockProject U 0 = 0 := by
  simp [blockProject]

@[simp] theorem blockEmbed_zero {M N D : Nat}
    (U : Fin (M * N) → EVector D) : blockEmbed U 0 = 0 := by
  simp [blockEmbed]

theorem blockProject_blockEmbed {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (z : BlockVec M N) :
    blockProject U (blockEmbed U z) = z := by
  unfold blockProject blockEmbed
  rw [WeaklyConvexLowerBound.Foundation.frameProject_frameEmbed hU]
  exact unflatten_flatten z

theorem blockSq_blockEmbed {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (z : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.vecSq (blockEmbed U z) = blockSq z := by
  unfold blockEmbed
  rw [WeaklyConvexLowerBound.Foundation.vecSq_frameEmbed hU, vecSq_flatten]

theorem blockSq_blockProject_le {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (X : EVector D) :
    blockSq (blockProject U X) ≤ WeaklyConvexLowerBound.Foundation.vecSq X := by
  unfold blockProject
  rw [← vecSq_flatten]
  simp only [flatten_unflatten]
  exact WeaklyConvexLowerBound.Foundation.vecSq_frameProject_le hU X

theorem blockProject_sub {M N D : Nat}
    (U : Fin (M * N) → EVector D) (X Y : EVector D) :
    blockProject U (X - Y) = blockProject U X - blockProject U Y := by
  unfold blockProject
  rw [← unflatten_sub, ← WeaklyConvexLowerBound.Foundation.frameProject_sub]

theorem blockEmbed_sub {M N D : Nat}
    (U : Fin (M * N) → EVector D) (x y : BlockVec M N) :
    blockEmbed U (x - y) = blockEmbed U x - blockEmbed U y := by
  unfold blockEmbed
  rw [flatten_sub, WeaklyConvexLowerBound.Foundation.frameEmbed_sub]

theorem blockProject_add {M N D : Nat}
    (U : Fin (M * N) → EVector D) (X Y : EVector D) :
    blockProject U (X + Y) = blockProject U X + blockProject U Y := by
  unfold blockProject WeaklyConvexLowerBound.Foundation.frameProject
  rw [← unflatten_add]
  congr 1
  funext i
  unfold WeaklyConvexLowerBound.Foundation.evecDotValue
  simp only [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

theorem blockEmbed_add {M N D : Nat}
    (U : Fin (M * N) → EVector D) (x y : BlockVec M N) :
    blockEmbed U (x + y) = blockEmbed U x + blockEmbed U y := by
  unfold blockEmbed WeaklyConvexLowerBound.Foundation.frameEmbed
  rw [flatten_add]
  funext k
  simp only [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

/-- Rotate a block objective by the hidden frame. -/
def rotatedValue {M N D : Nat}
    (f : BlockVec M N → ℝ) (U : Fin (M * N) → EVector D) : EVector D → ℝ :=
  fun X => f (blockProject U X)

/-- The ambient quadratic-support relation. -/
def EVectorQSubgradient {D : Nat} (c : ℝ) (f : EVector D → ℝ)
    (X G : EVector D) : Prop :=
  ∀ Y, f X + WeaklyConvexLowerBound.Foundation.evecDotValue G (Y - X) -
      c * WeaklyConvexLowerBound.Foundation.vecSq (Y - X) ≤ f Y

/-- A block quadratic-support subgradient lifts to a quadratic-support
subgradient of the rotated objective. -/
theorem qSubgradient_rotate {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {c : ℝ} (hc : 0 ≤ c) {f : BlockVec M N → ℝ} {z g : BlockVec M N}
    (hg : QSubgradient c f z g) :
    EVectorQSubgradient c (rotatedValue f U)
      (blockEmbed U z) (blockEmbed U g) := by
  intro Y
  have hproj : blockProject U (blockEmbed U z) = z :=
    blockProject_blockEmbed hU z
  have hsupport := hg (blockProject U Y)
  have hdot :
      WeaklyConvexLowerBound.Foundation.evecDotValue (blockEmbed U g)
          (Y - blockEmbed U z) =
        blockDot g (blockProject U Y - z) := by
    unfold blockEmbed blockProject
    rw [WeaklyConvexLowerBound.Foundation.evecDotValue_frameEmbed_left]
    change (∑ i : Fin (M * N), flatten g i *
      WeaklyConvexLowerBound.Foundation.frameProject U (Y -
        WeaklyConvexLowerBound.Foundation.frameEmbed U (flatten z)) i) = _
    rw [← WeaklyConvexLowerBound.Foundation.frameProject_sub,
      WeaklyConvexLowerBound.Foundation.frameProject_frameEmbed hU]
    rw [← evecDotValue_flatten]
    congr 1
    rw [flatten_sub]
    simp only [flatten_unflatten]
  have hnorm :
      blockSq (blockProject U Y - z) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (Y - blockEmbed U z) := by
    calc
      blockSq (blockProject U Y - z) =
          blockSq (blockProject U (Y - blockEmbed U z)) := by
        rw [blockProject_sub, hproj]
      _ ≤ WeaklyConvexLowerBound.Foundation.vecSq (Y - blockEmbed U z) :=
        blockSq_blockProject_le hU _
  unfold rotatedValue
  rw [hproj, hdot]
  nlinarith

/-! ## Proximal-point covariance -/

/-- Ambient counterpart of `IsHalfProxPoint`, using the same squared-norm
normalization as the paper's parameter `1/2`. -/
def EVectorIsHalfProxPoint {D : Nat} (f : EVector D → ℝ)
    (Y Z : EVector D) : Prop :=
  ∀ X, f Z + WeaklyConvexLowerBound.Foundation.vecSq (Z - Y) ≤
    f X + WeaklyConvexLowerBound.Foundation.vecSq (X - Y)

/-- Keep the orthogonal component of `Y` and replace only its hidden-frame
coordinates by `z`. -/
def ambientProxLift {M N D : Nat}
    (U : Fin (M * N) → EVector D) (Y : EVector D)
    (z : BlockVec M N) : EVector D :=
  Y + blockEmbed U (z - blockProject U Y)

theorem blockProject_ambientProxLift {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (Y : EVector D) (z : BlockVec M N) :
    blockProject U (ambientProxLift U Y z) = z := by
  unfold ambientProxLift
  rw [blockProject_add, blockProject_blockEmbed hU]
  ext m j
  simp

theorem ambientProxLift_sub {M N D : Nat}
    (U : Fin (M * N) → EVector D) (Y : EVector D)
    (z : BlockVec M N) :
    ambientProxLift U Y z - Y =
      blockEmbed U (z - blockProject U Y) := by
  unfold ambientProxLift
  abel

theorem vecSq_ambientProxLift_sub {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (Y : EVector D) (z : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.vecSq (ambientProxLift U Y z - Y) =
      blockSq (z - blockProject U Y) := by
  rw [ambientProxLift_sub, blockSq_blockEmbed hU]

/-- A proximal point of the block function lifts to a proximal point of the
rotated ambient function, with exactly the same residual norm. -/
theorem IsHalfProxPoint.rotate {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {f : BlockVec M N → ℝ} {Y : EVector D} {z : BlockVec M N}
    (hz : IsHalfProxPoint f (blockProject U Y) z) :
    EVectorIsHalfProxPoint (rotatedValue f U) Y
      (ambientProxLift U Y z) := by
  intro X
  have hbase := hz (blockProject U X)
  have hcontract :
      blockSq (blockProject U X - blockProject U Y) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (X - Y) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  unfold rotatedValue
  rw [blockProject_ambientProxLift hU,
    vecSq_ambientProxLift_sub hU]
  linarith

/-- Conversely, projecting any ambient proximal point gives a block
proximal point.  This direction is needed to show that rotations cannot
create spurious small-stationarity points. -/
theorem EVectorIsHalfProxPoint.project {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {f : BlockVec M N → ℝ} {Y Z : EVector D}
    (hZ : EVectorIsHalfProxPoint (rotatedValue f U) Y Z) :
    IsHalfProxPoint f (blockProject U Y) (blockProject U Z) := by
  intro x
  let X : EVector D := ambientProxLift U Y x
  have hmin := hZ X
  have hleft :
      blockSq (blockProject U Z - blockProject U Y) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (Z - Y) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  have hPX : blockProject U X = x := by
    exact blockProject_ambientProxLift hU Y x
  have hnormX : WeaklyConvexLowerBound.Foundation.vecSq (X - Y) =
      blockSq (x - blockProject U Y) := by
    exact vecSq_ambientProxLift_sub hU Y x
  unfold rotatedValue at hmin
  rw [hPX, hnormX] at hmin
  linarith

end

end WeaklyConvexLowerBound


