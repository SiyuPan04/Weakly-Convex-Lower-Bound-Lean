import WC.PrefixChainResponse
import WC.MaskedLocality
import WC.NormalizedChain
import WC.CoreEmbedding

/-! Exact prefix responses for the true normalized objective, including its
entire Frechet subdifferential, on the robust diagonal tube. -/

noncomputable section
namespace WC
open scoped Classical
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def isometryChainPrefix {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E)
    (s : Finset (Fin M × Fin N)) : ChainPrefix M N s E :=
  ⟨fun i => U (EuclideanSpace.basisFun (Fin M × Fin N) ℝ i.val),
    ((EuclideanSpace.basisFun (Fin M × Fin N) ℝ).orthonormal.comp
      (fun i : {i // i ∈ s} => i.val) Subtype.val_injective).comp_linearIsometry U⟩

theorem isometryProjection_coordinate {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E)
    (x : E) (i : Fin M × Fin N) :
    isometryProjection U x i = inner ℝ (U (EuclideanSpace.basisFun (Fin M × Fin N) ℝ i)) x := by
  have h := U.toContinuousLinearMap.adjoint_inner_right
    (EuclideanSpace.basisFun (Fin M × Fin N) ℝ i) x
  change inner ℝ (EuclideanSpace.basisFun (Fin M × Fin N) ℝ i) (isometryProjection U x) = _ at h
  rwa [EuclideanSpace.basisFun_inner] at h

theorem prefixCoordinates_isometryChainPrefix_apply {M N : ℕ}
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (s : Finset (Fin M × Fin N)) (x : E) (i : Fin M × Fin N) :
    prefixCoordinates s (isometryChainPrefix U s).val x i =
      if i ∈ s then isometryProjection U x i else 0 := by
  by_cases hi : i ∈ s
  · simp only [prefixCoordinates, PiLp.toLp_apply, dif_pos hi, if_pos hi, isometryChainPrefix]
    exact (isometryProjection_coordinate U x i).symm
  · simp only [prefixCoordinates, PiLp.toLp_apply, dif_neg hi, if_neg hi]

theorem prefixCoordinates_isometryChainPrefix_diagonalMask {M N : ℕ}
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (r : ℕ) (x : E) :
    prefixCoordinates (exposedIndices M N r) (isometryChainPrefix U (exposedIndices M N r)).val x =
      diagonalMask M N r (isometryProjection U x) := by
  apply PiLp.ext
  intro i
  rw [prefixCoordinates_isometryChainPrefix_apply, diagonalMask_apply]
  simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normalizedChainWall_prefix_eventuallyEq {M N : ℕ}
    (hM : 1 ≤ M) (hN : 256 ≤ N) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (r : ℕ)
    (hidden : isometryProjection U ((2 / 3 : ℝ) • x) ∈ diagonalTube M N r) :
    normalizedChainWall U =ᶠ[𝓝 x]
      prefixChainWall (exposedIndices M N (r + 1))
        (isometryChainPrefix U (exposedIndices M N (r + 1))) := by
  have hP : Continuous (fun y : E => isometryProjection U ((2 / 3 : ℝ) • y)) :=
    (isometryProjection U).continuous.comp (continuous_const.smul continuous_id)
  have hlocal := (chainMajorant_diagonalMask_eventuallyEq hM hN _ r hidden).comp_tendsto
    hP.continuousAt
  filter_upwards [hlocal] with y hy
  dsimp only [Function.comp_def] at hy
  rw [prefixChainWall_formula, prefixCoordinates_isometryChainPrefix_diagonalMask]
  change (1 / 2 : ℝ) * max (chainMajorant (isometryProjection U ((2 / 3 : ℝ) • y)))
    (chainMajorant (isometryProjection U (0 : E)) + 3 *
      (‖(2 / 3 : ℝ) • y‖ - chainWallRadius M N)) = _
  rw [map_zero, hy]

variable [ProperSpace E] [FiniteDimensional ℝ E]

theorem normalizedChainWall_prefix_fullOracle {M N : ℕ}
    (hM : 0 < M) (hN : 256 ≤ N) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (r : ℕ)
    (hidden : isometryProjection U ((2 / 3 : ℝ) • x) ∈ diagonalTube M N r) :
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (normalizedChainWall_admissible hM hN U).lipschitz
      (normalizedChainWall_admissible hM hN U).weaklyConvex x =
    prefixChainResponse hM hN (exposedIndices M N (r + 1))
      (x, isometryChainPrefix U (exposedIndices M N (r + 1))) := by
  exact fullOracle_congr_eventuallyEq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (normalizedChainWall_admissible hM hN U).lipschitz
    (prefixChainWall_admissible hM hN _ _).lipschitz
    (normalizedChainWall_admissible hM hN U).weaklyConvex
    (prefixChainWall_admissible hM hN _ _).weaklyConvex x
    (normalizedChainWall_prefix_eventuallyEq (by omega) hN U x r hidden)

theorem isometryChainPrefix_rotatedCore {M N d : ℕ}
    (e : Fin M × Fin N ↪ Fin d) (g : Frame.Orthogonal (Rotation.Normalized.Ambient d))
    (s : Finset (Fin M × Fin N)) :
    isometryChainPrefix (rotatedCore e g) s =
      relabelPrefix e s (Rotation.Normalized.framePrefix (s.image e) g) := by
  apply Subtype.ext
  funext i
  exact rotatedCore_basis e g i.val

theorem normalizedChainWall_rotated_prefix_fullOracle {M N d : ℕ}
    (hM : 0 < M) (hN : 256 ≤ N) (e : Fin M × Fin N ↪ Fin d)
    (g : Frame.Orthogonal (Rotation.Normalized.Ambient d)) (x : Rotation.Normalized.Ambient d) (r : ℕ)
    (hidden : ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) →
      |inner ℝ (Rotation.Normalized.coordinates g (e i)) x| < normalizedChainTolerance M N) :
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (normalizedChainWall_admissible hM hN (rotatedCore e g)).lipschitz
      (normalizedChainWall_admissible hM hN (rotatedCore e g)).weaklyConvex x =
    prefixChainResponse hM hN (exposedIndices M N (r + 1))
      (x, relabelPrefix e (exposedIndices M N (r + 1))
        (Rotation.Normalized.framePrefix ((exposedIndices M N (r + 1)).image e) g)) := by
  have hsmall : isometryProjection (rotatedCore e g) ((2 / 3 : ℝ) • x) ∈ diagonalTube M N r := by
    intro i hi
    rw [rotatedCore_projection_coordinate, real_inner_smul_right, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    have hh := hidden i hi
    dsimp only [normalizedChainTolerance] at hh
    linarith
  have h := normalizedChainWall_prefix_fullOracle hM hN (rotatedCore e g) x r hsmall
  rwa [isometryChainPrefix_rotatedCore] at h

end WC
