import WC.CoreFiltration
import WC.CoreRotation
import WC.PrefixChainResponse
import WC.LowerReduction
import WC.MaskedLocality
import WC.PrefixOracleLocality
import WC.NormalizedExterior

/-! Assembly of the concrete normalized rotated family. The response is
the genuine full oracle of the zero-filled prefix objective, defined on
every orthonormal prefix. -/

noncomputable section
namespace WC
open scoped BigOperators Classical
open Rotation.Normalized

def normalizedChainResponse {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 0 < M) (hN : 256 ≤ N) (t : ℕ)
    (p : Model.Space d × Prefix (diagonalExposed e t)) : Model.Reply d :=
  prefixChainResponse hM hN (exposedIndices M N (t + 1))
    (p.1, relabelPrefix e (exposedIndices M N (t + 1)) p.2)

theorem normalizedChainResponse_measurable {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 0 < M) (hN : 256 ≤ N) (t : ℕ) :
    @Measurable _ _ (borel _) (borel _) (normalizedChainResponse e hM hN t) := by
  have hcont : Continuous (fun p : Model.Space d × Prefix (diagonalExposed e t) =>
      (p.1, relabelPrefix e (exposedIndices M N (t + 1)) p.2)) :=
    continuous_fst.prodMk ((relabelPrefix_continuous e (exposedIndices M N (t + 1))).comp continuous_snd)
  have h : Measurable (normalizedChainResponse e hM hN t) :=
    (prefixChainResponse_measurable hM hN (exposedIndices M N (t + 1))).comp hcont.measurable
  exact h.mono (le_of_eq BorelSpace.measurable_eq) (le_of_eq BorelSpace.measurable_eq.symm)

theorem normalizedChain_terminal_barrier {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 2 ≤ M) (hN : 256 ≤ N) (hMmax : M ≤ 2 ^ (8 * N))
    (g : Frame.Orthogonal (Model.Space d)) (x : Model.Space d)
    (hidden : ∀ i ∈ coreLabels e, i ∉ diagonalExposed e ((M - 1) * stagger N - 1) →
      |inner ℝ (coordinates g i) x| < normalizedChainTolerance M N) :
    1 / (32 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 2) (normalizedChainWall (rotatedCore e g))) x‖ := by
  have hMpos : 0 < M := by omega
  have hNpos : 0 < N := by omega
  have hTpos := diagonal_horizon_positive hM hN
  apply normalizedChainWall_terminal_barrier hMpos hN hMmax (rotatedCore e g) x
    (terminalBlock (N := N) hMpos) (by rw [terminalBlock_card])
  intro i hi
  have hlabel : e i ∈ coreLabels e := Finset.mem_image_of_mem e (Finset.mem_univ i)
  have hnot : e i ∉ diagonalExposed e ((M - 1) * stagger N - 1) := by
    intro hh
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hh
    have heq : j = i := e.injective hij
    subst j
    have hTime : (M - 1) * stagger N - 1 + 1 = (M - 1) * stagger N := by omega
    rw [hTime] at hj
    exact terminalBlock_hidden hMpos hi hj
  have hx := hidden (e i) hlabel hnot
  rw [rotatedCore_projection_coordinate, real_inner_smul_right]
  have hη := robustTolerance_le_inv_N M hNpos
  have habs := le_abs_self (inner ℝ (coordinates g (e i)) x)
  dsimp only [normalizedChainTolerance] at hx
  nlinarith

theorem mem_previous_diagonalExposed_iff {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (i : Fin M × Fin N) (t : ℕ) :
    e i ∈ previous (diagonalExposed e) t ↔ diagonalLevel N (i.1.val, i.2.val) < t := by
  cases t with
  | zero => simp [previous]
  | succ t =>
    change e i ∈ (exposedIndices M N (t + 1)).image e ↔ _
    constructor
    · intro h
      obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp h
      have heq : j = i := e.injective hij
      subst j
      exact (Finset.mem_filter.mp hj).2
    · intro h
      apply Finset.mem_image_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩

theorem normalizedChainRadius_pos (M N : ℕ) (hN : 256 ≤ N) : 0 < normalizedChainRadius M N := by
  have hR := chainWallRadius_ge_one M N hN
  dsimp only [normalizedChainRadius]
  linarith

theorem normalizedChainTolerance_pos (M N : ℕ) (hN : 0 < N) : 0 < normalizedChainTolerance M N := by
  exact mul_pos (by norm_num) (robustTolerance_pos M hN)

/-- The manuscript's concrete normalized chain satisfies every abstract
rotation hypothesis, including the complete oracle on all prefixes. -/
def normalizedChainFamily {M N d : ℕ} [NeZero d] (e : Fin M × Fin N ↪ Fin d)
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
  radius := normalizedChainRadius M N
  tolerance := normalizedChainTolerance M N
  radius_positive := normalizedChainRadius_pos M N hN
  tolerance_positive := normalizedChainTolerance_pos M N (by omega)
  objective := fun g => normalizedChainWall (rotatedCore e g)
  regularity := fun g => normalizedChainWall_admissible (by omega) hN (rotatedCore e g)
  response := normalizedChainResponse e (by omega) hN
  measurable_response := normalizedChainResponse_measurable e (by omega) hN
  outside := normalizedChainOutside e (by omega) hN
  measurable_outside := by
    have h := normalizedChainOutside_measurable e (by omega : 0 < M) hN
    exact h.mono (le_of_eq BorelSpace.measurable_eq) (le_of_eq BorelSpace.measurable_eq.symm)
  locality := by
    intro t _ g x _ hidden
    apply normalizedChainWall_rotated_prefix_fullOracle (by omega) hN e g x t
    intro i hi
    apply hidden (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))
    intro hprev
    have hlevel := (mem_previous_diagonalExposed_iff e i t).mp hprev
    omega
  terminal_barrier := by
    intro g x _ hidden
    exact normalizedChain_terminal_barrier e hM hN hMmax g x hidden
  exterior := by
    intro g x hx
    exact ⟨normalizedChainWall_exterior_oracle e (by omega) hN g x hx,
      normalizedChainWall_exterior_gradient (by omega) hN (rotatedCore e g) x hx.le⟩
  measurable_oracle := normalizedChain_joint_oracle_measurable e (by omega) hN
  measurable_gradient := (normalizedChain_joint_gradient_continuous e (by omega) hN).measurable

/-- Concrete construction discharging the only family premise of the
physical large-regime lower reduction. Its radius and tolerance are
independent of the ambient dimension and confidence level. -/
theorem normalizedChain_uniformFamilies : LowerReduction.UniformFamilies := by
  intro M N hN hM hMmax
  refine ⟨(M - 1) * stagger N, normalizedChainRadius M N, normalizedChainTolerance M N,
    normalizedChainRadius_pos M N hN, normalizedChainTolerance_pos M N (by omega), ?_⟩
  intro d hd hdim
  letI : NeZero d := hd
  let e := coreEmbedding M N d (by omega : M * N ≤ d)
  exact ⟨normalizedChainFamily e hM hN hMmax, rfl, rfl⟩

end WC
