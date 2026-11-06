import WC.CoreRotation
import WC.ParametricOracle
import WC.MaskedLocality

/-! Joint complete-oracle measurability and a globally defined exterior
response independent of the unknown rotation. -/

noncomputable section
namespace WC
open Filter Topology

theorem normalizedChain_joint_continuous {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 0 < M) (hN : 256 ≤ N) :
    Continuous (fun p : Frame.Orthogonal (Model.Space d) × Model.Space d =>
      normalizedChainWall (rotatedCore e p.1) p.2) := by
  simp_rw [normalizedChainWall_rotatedCore]
  exact ((normalizedChainWall_admissible hM hN (coordinateEmbedding e)).lipschitz.continuous
    (by norm_num)).comp rotationProjection_continuous

theorem normalizedChain_joint_oracle_measurable {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 0 < M) (hN : 256 ≤ N) :
    Measurable (fun p : Frame.Orthogonal (Model.Space d) × Model.Space d =>
      fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        (normalizedChainWall_admissible hM hN (rotatedCore e p.1)).lipschitz
        (normalizedChainWall_admissible hM hN (rotatedCore e p.1)).weaklyConvex p.2) := by
  exact parameterized_fullOracle_measurable (α := Frame.Orthogonal (Model.Space d))
    (f := fun g => normalizedChainWall (rotatedCore e g)) (by norm_num) (by norm_num)
    (normalizedChain_joint_continuous e hM hN)
    (fun g => (normalizedChainWall_admissible hM hN (rotatedCore e g)).lipschitz)
    (fun g => (normalizedChainWall_admissible hM hN (rotatedCore e g)).weaklyConvex)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E]

theorem normalizedChainWall_eventuallyEq_exterior {M N : ℕ} (hN : 256 ≤ N)
    (U V : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : normalizedChainRadius M N < ‖x‖) :
    normalizedChainWall U =ᶠ[𝓝 x] normalizedChainWall V := by
  have hNpos : 0 < N := by omega
  have hULip := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hVLip := isometricLift_lipschitz V (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  have hrad : 3 * chainWallRadius M N < ‖(2 / 3 : ℝ) • y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    dsimp [normalizedChainRadius] at hy
    have hR := chainWallRadius_ge_one M N hN
    linarith
  change (1 / 2 : ℝ) * radialWall (isometricLift U chainMajorant) (chainWallRadius M N) ((2 / 3 : ℝ) • y) =
    (1 / 2 : ℝ) * radialWall (isometricLift V chainMajorant) (chainWallRadius M N) ((2 / 3 : ℝ) • y)
  rw [radialWall_eq_outside hULip hrad, radialWall_eq_outside hVLip hrad]
  simp only [radialBranch, isometricLift, map_zero]

def normalizedChainOutside {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) (hM : 0 < M) (hN : 256 ≤ N) :
    Model.Space d → Model.Reply d :=
  fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).lipschitz
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).weaklyConvex

theorem normalizedChainOutside_measurable {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 0 < M) (hN : 256 ≤ N) : Measurable (normalizedChainOutside e hM hN) :=
  fullOracle_measurable (by norm_num) (by norm_num)
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).lipschitz
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).weaklyConvex

theorem normalizedChainWall_exterior_oracle {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 0 < M) (hN : 256 ≤ N) (g : Frame.Orthogonal (Model.Space d)) (x : Model.Space d)
    (hx : normalizedChainRadius M N < ‖x‖) :
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (normalizedChainWall_admissible hM hN (rotatedCore e g)).lipschitz
      (normalizedChainWall_admissible hM hN (rotatedCore e g)).weaklyConvex x = normalizedChainOutside e hM hN x :=
  fullOracle_congr_eventuallyEq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (normalizedChainWall_admissible hM hN (rotatedCore e g)).lipschitz
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).lipschitz
    (normalizedChainWall_admissible hM hN (rotatedCore e g)).weaklyConvex
    (normalizedChainWall_admissible hM hN (coordinateEmbedding e)).weaklyConvex x
    (normalizedChainWall_eventuallyEq_exterior hN _ _ x hx)

end WC
