import MP.Prefix
import MP.RadialOracle
import WC.NormalizedFamily

/-! The concrete MP radial objective with its prescribed radius fills
every full-oracle hypothesis of the proved rotation framework. -/

noncomputable section
namespace MP
open WC Filter Topology
open WC.Rotation.Normalized
open scoped Classical
set_option maxHeartbeats 600000

theorem radialObjective_rotatedCore {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (g : Frame.Orthogonal (WC.Model.Space d)) :
    radialObjective (rotatedCore e g) = isometricLift (Frame.act _ g).toLinearIsometry
      (radialObjective (coordinateEmbedding e)) := by
  funext x
  simp only [radialObjective, radialObjectiveAt, isometricLift, rotatedCore_projection]
  rw [rotationProjection_norm]

theorem radial_joint_gradient_continuous {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 2 ≤ M) (hN : 256 ≤ N) :
    Continuous (fun p : Frame.Orthogonal (WC.Model.Space d) × WC.Model.Space d =>
      gradient (moreauEnvelope (1 / 2) (radialObjective (rotatedCore e p.1))) p.2) := by
  simp_rw [radialObjective_rotatedCore]
  have h := radial_admissible hM hN (coordinateEmbedding e)
  simpa only [mul_one] using rotated_moreau_gradient_continuous
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) h.lipschitz h.weaklyConvex

theorem radial_joint_continuous {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 2 ≤ M) (hN : 256 ≤ N) :
    Continuous (fun p : Frame.Orthogonal (WC.Model.Space d) × WC.Model.Space d =>
      radialObjective (rotatedCore e p.1) p.2) := by
  simp_rw [radialObjective_rotatedCore]
  exact ((radial_admissible hM hN (coordinateEmbedding e)).lipschitz.continuous
    (by norm_num)).comp rotationProjection_continuous

theorem radial_joint_oracle_measurable {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 2 ≤ M) (hN : 256 ≤ N) :
    Measurable (fun p : Frame.Orthogonal (WC.Model.Space d) × WC.Model.Space d =>
      fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        (radial_admissible hM hN (rotatedCore e p.1)).lipschitz
        (radial_admissible hM hN (rotatedCore e p.1)).weaklyConvex p.2) :=
  parameterized_fullOracle_measurable (α := Frame.Orthogonal (WC.Model.Space d))
    (f := fun g => radialObjective (rotatedCore e g)) (by norm_num) (by norm_num)
    (radial_joint_continuous e hM hN)
    (fun g => (radial_admissible hM hN (rotatedCore e g)).lipschitz)
    (fun g => (radial_admissible hM hN (rotatedCore e g)).weaklyConvex)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem prefixObjectiveAt_eq_truncated {M N : ℕ} (R : ℝ)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (r : ℕ) :
    prefixObjectiveAt R (exposedIndices M N r) (isometryChainPrefix U (exposedIndices M N r)) =
      truncatedRadialObjectiveAt R U r := by
  funext x
  simp only [prefixObjectiveAt, prefixChainBase, truncatedRadialObjectiveAt,
    prefixCoordinates_isometryChainPrefix_diagonalMask]

variable [ProperSpace E]

theorem radial_prefix_fullOracle {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (r : ℕ)
    (hidden : isometryProjection U ((2 / 3 : ℝ) • x) ∈ diagonalTube M N r) :
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (radial_admissible hM hN U).lipschitz (radial_admissible hM hN U).weaklyConvex x =
    prefixResponse (by omega : 0 < M) hN (exposedIndices M N (r + 1))
      (x, isometryChainPrefix U (exposedIndices M N (r + 1))) := by
  apply fullOracle_congr_eventuallyEq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := radialObjectiveAt_prefix_eventuallyEq (by omega) hN (radialRadius M N) U x r hidden
  rw [← prefixObjectiveAt_eq_truncated] at h
  exact h

def chainResponse {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) (t : ℕ)
    (p : WC.Model.Space d × Prefix (diagonalExposed e t)) : WC.Model.Reply d :=
  prefixResponse (by omega : 0 < M) hN (exposedIndices M N (t + 1))
    (p.1, relabelPrefix e (exposedIndices M N (t + 1)) p.2)

theorem chainResponse_measurable {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) (t : ℕ) :
    @Measurable _ _ (borel _) (borel _) (chainResponse e hM hN t) := by
  have hcont : Continuous (fun p : WC.Model.Space d × Prefix (diagonalExposed e t) =>
      (p.1, relabelPrefix e (exposedIndices M N (t + 1)) p.2)) :=
    continuous_fst.prodMk ((relabelPrefix_continuous e (exposedIndices M N (t + 1))).comp continuous_snd)
  have h : Measurable (chainResponse e hM hN t) :=
    (prefixResponse_measurable (by omega : 0 < M) hN (exposedIndices M N (t + 1))).comp hcont.measurable
  exact h.mono (le_of_eq BorelSpace.measurable_eq) (le_of_eq BorelSpace.measurable_eq.symm)

theorem radial_terminal_barrier {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) (hMmax : M ≤ 2 ^ (8 * N))
    (g : Frame.Orthogonal (WC.Model.Space d)) (x : WC.Model.Space d)
    (hidden : ∀ i ∈ coreLabels e, i ∉ diagonalExposed e ((M - 1) * stagger N - 1) →
      |inner ℝ (coordinates g i) x| < normalizedChainTolerance M N) :
    1 / (32 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 2) (radialObjective (rotatedCore e g))) x‖ := by
  have hMpos : 0 < M := by omega
  have hTpos := diagonal_horizon_positive hM hN
  apply radial_moreau_barrier hM hN hMmax (rotatedCore e g) x
    (terminalBlock (N := N) hMpos) (by rw [terminalBlock_card])
  intro i hi
  have hnot : e i ∉ diagonalExposed e ((M - 1) * stagger N - 1) := by
    intro hh
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hh
    have heq : j = i := e.injective hij
    subst j
    have hTime : (M - 1) * stagger N - 1 + 1 = (M - 1) * stagger N := by omega
    rw [hTime] at hj
    exact terminalBlock_hidden hMpos hi hj
  have hx := hidden (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i)) hnot
  rw [rotatedCore_projection_coordinate, real_inner_smul_right]
  have habs := le_abs_self (inner ℝ (coordinates g (e i)) x)
  dsimp only [normalizedChainTolerance] at hx
  nlinarith

def chainOutside {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) (hM : 2 ≤ M) (hN : 256 ≤ N) :
    WC.Model.Space d → WC.Model.Reply d :=
  fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (radial_admissible hM hN (coordinateEmbedding e)).lipschitz
    (radial_admissible hM hN (coordinateEmbedding e)).weaklyConvex

theorem chainOutside_measurable {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) : Measurable (chainOutside e hM hN) :=
  fullOracle_measurable (by norm_num) (by norm_num)
    (radial_admissible hM hN (coordinateEmbedding e)).lipschitz
    (radial_admissible hM hN (coordinateEmbedding e)).weaklyConvex

/-- The actual prescribed-radius family, available in every sufficiently
large ambient dimension. All response maps use the entire oracle. -/
def chainFamily {M N d : ℕ} [NeZero d] (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) (hMmax : M ≤ 2 ^ (8 * N)) :
    Family d M N ((M - 1) * stagger N) where
  horizon_positive := diagonal_horizon_positive hM hN
  core := coreLabels e
  core_card := coreLabels_card e
  exposed := diagonalExposed e
  exposed_mono := diagonalExposed_mono e
  exposed_subset := fun t _ => diagonalExposed_subset e t
  exposed_proper := fun _ ht => diagonalExposed_proper e (by omega) (by omega) ht
  width := fun t _ => diagonalExposed_width e hN t
  horizon_bound := WC.horizon_bound hM hN
  radius := 4 * radialRadius M N
  tolerance := normalizedChainTolerance M N
  radius_positive := mul_pos (by norm_num) (radialRadius_pos (by omega))
  tolerance_positive := normalizedChainTolerance_pos M N (by omega)
  objective := fun g => radialObjective (rotatedCore e g)
  regularity := fun g => radial_admissible hM hN (rotatedCore e g)
  response := chainResponse e hM hN
  measurable_response := chainResponse_measurable e hM hN
  outside := chainOutside e hM hN
  measurable_outside := by
    have h := chainOutside_measurable e hM hN
    exact h.mono (le_of_eq BorelSpace.measurable_eq) (le_of_eq BorelSpace.measurable_eq.symm)
  locality := by
    intro t _ g x _ hidden
    have hsmall : isometryProjection (rotatedCore e g) ((2 / 3 : ℝ) • x) ∈ diagonalTube M N t := by
      intro i hi
      have hh := hidden (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i)) (by
        intro hprev
        have hlevel := (mem_previous_diagonalExposed_iff e i t).mp hprev
        omega)
      rw [rotatedCore_projection_coordinate, real_inner_smul_right, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
      dsimp only [normalizedChainTolerance] at hh
      linarith
    have h := radial_prefix_fullOracle hM hN (rotatedCore e g) x t hsmall
    rwa [isometryChainPrefix_rotatedCore] at h
  terminal_barrier := by
    intro g x _ hidden
    exact radial_terminal_barrier e hM hN hMmax g x hidden
  exterior := by
    intro g x hx
    refine ⟨?_, radial_exterior_gradient hM hN (rotatedCore e g) x hx.le⟩
    have hR := radialRadius_pos (N := N) (show 0 < M by omega)
    exact radialObjectiveAt_exterior_fullOracle_eq hM hN hR.le (rotatedCore e g)
      (coordinateEmbedding e) x (by linarith)
  measurable_oracle := radial_joint_oracle_measurable e hM hN
  measurable_gradient := (radial_joint_gradient_continuous e hM hN).measurable

end MP
