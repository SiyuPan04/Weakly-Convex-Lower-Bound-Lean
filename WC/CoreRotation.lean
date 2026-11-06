import WC.CoreEmbedding
import WC.NormalizedChain
import WC.RotatedOracle

/-! The concrete normalized chain family is an orthogonal rotation of a
single fixed objective. In particular its actual gradient is jointly Borel. -/

noncomputable section
namespace WC

theorem rotationProjection_norm {d : ℕ} (g : Frame.Orthogonal (Model.Space d)) (x : Model.Space d) :
    ‖isometryProjection (Frame.act _ g).toLinearIsometry x‖ = ‖x‖ := by
  change ‖((Frame.act _ g : Model.Space d ≃ₗᵢ[ℝ] Model.Space d) : Model.Space d →L[ℝ] Model.Space d).adjoint x‖ = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact (Frame.act _ g).symm.norm_map x

theorem normalizedChainWall_rotatedCore {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (g : Frame.Orthogonal (Model.Space d)) :
    normalizedChainWall (rotatedCore e g) = isometricLift (Frame.act _ g).toLinearIsometry
      (normalizedChainWall (coordinateEmbedding e)) := by
  funext x
  simp only [normalizedChainWall, scaleFunction, liftedChainWall, radialWall, radialBranch,
    isometricLift, rotatedCore_projection, map_smul, map_zero]
  rw [norm_smul, norm_smul, rotationProjection_norm]

theorem normalizedChain_joint_gradient_continuous {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 0 < M) (hN : 256 ≤ N) :
    Continuous (fun p : Frame.Orthogonal (Model.Space d) × Model.Space d =>
      gradient (moreauEnvelope (1 / 2) (normalizedChainWall (rotatedCore e p.1))) p.2) := by
  simp_rw [normalizedChainWall_rotatedCore]
  have h := normalizedChainWall_admissible hM hN (coordinateEmbedding e)
  simpa only [mul_one] using rotated_moreau_gradient_continuous
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) h.lipschitz h.weaklyConvex

end WC
