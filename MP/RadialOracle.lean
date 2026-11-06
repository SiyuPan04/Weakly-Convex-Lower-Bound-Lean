import MP.Radial

/-! Exact exterior and robust masked identities for the full MP oracle. -/

noncomputable section
namespace MP
open WC Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem radial_firstBranch_lipschitz {M N : ℕ} (hN : 0 < N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    GloballyLipschitz (2 / 3 : ℝ) (fun x : E =>
      (1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U x)) := by
  have hl := lipschitz_scale (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hN))
  norm_num at hl
  have heq : scaleFunction (1 / 2) (2 / 3) (isometricLift U chainMajorant) =
      (fun x => (1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U x)) := by
    funext x
    simp only [scaleFunction, isometricLift, map_smul]
  rw [heq] at hl
  exact hl

theorem radialObjectiveAt_eq_outside {M N : ℕ} (hN : 0 < N)
    (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 3 * R < ‖x‖) :
    radialObjectiveAt R U x = (1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖x‖ - R := by
  apply max_eq_right
  have hl := (le_abs_self ((1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U x) -
    (1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U 0))).trans
      (radial_firstBranch_lipschitz hN U x 0)
  simp only [map_zero, smul_zero, sub_zero] at hl
  linarith

theorem radialObjectiveAt_eventuallyEq_outside {M N : ℕ} (hN : 0 < N)
    (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 3 * R < ‖x‖) :
    radialObjectiveAt R U =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖y‖ - R) := by
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact radialObjectiveAt_eq_outside hN R U y hy

theorem radialObjectiveAt_subdifferential_outside {M N : ℕ} (hN : 0 < N)
    {R : ℝ} (hR : 0 < R) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 3 * R < ‖x‖) :
    subdifferential (radialObjectiveAt R U) x = {‖x‖⁻¹ • x} := by
  have hxne : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hg : HasGradientAt (fun y : E => (1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖y‖ - R)
      (‖x‖⁻¹ • x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    exact ((hasGradientAt_norm_of_ne_zero hxne).hasFDerivAt.const_add
      ((1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N))).sub_const R
  ext v
  exact (frechetSubgradient_congr_eventuallyEq
    (radialObjectiveAt_eventuallyEq_outside hN R U x hx)).trans (frechetSubgradient_iff_gradient hg)

def truncatedRadialObjectiveAt {M N : ℕ} (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E)
    (r : ℕ) (x : E) : ℝ :=
  max ((1 / 2 : ℝ) * chainMajorant (diagonalMask M N r (isometryProjection U ((2 / 3 : ℝ) • x))))
    ((1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖x‖ - R)

theorem radialObjectiveAt_prefix_eventuallyEq {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (r : ℕ)
    (hidden : isometryProjection U ((2 / 3 : ℝ) • x) ∈ diagonalTube M N r) :
    radialObjectiveAt R U =ᶠ[𝓝 x] truncatedRadialObjectiveAt R U (r + 1) := by
  have hP : Continuous (fun y : E => isometryProjection U ((2 / 3 : ℝ) • y)) :=
    (isometryProjection U).continuous.comp (continuous_const.smul continuous_id)
  have hlocal := (chainMajorant_diagonalMask_eventuallyEq hM hN _ r hidden).comp_tendsto hP.continuousAt
  filter_upwards [hlocal] with y hy
  dsimp only [Function.comp_def] at hy
  change max ((1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U y)) _ = _
  rw [map_smul] at hy
  rw [hy]
  simp only [truncatedRadialObjectiveAt, map_smul]

variable [ProperSpace E]

theorem radial_exterior_oracle {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 4 * radialRadius M N ≤ ‖x‖) :
    (fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (radial_admissible hM hN U).lipschitz (radial_admissible hM hN U).weaklyConvex x).1 =
      (1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖x‖ - radialRadius M N ∧
    ((fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (radial_admissible hM hN U).lipschitz (radial_admissible hM hN U).weaklyConvex x).2.val : Set E) =
      {‖x‖⁻¹ • x} := by
  have hR := radialRadius_pos (N := N) (show 0 < M by omega)
  have hx' : 3 * radialRadius M N < ‖x‖ := by linarith
  exact ⟨radialObjectiveAt_eq_outside (by omega) _ U x hx',
    radialObjectiveAt_subdifferential_outside (by omega) hR U x hx'⟩

theorem radialObjectiveAt_exterior_fullOracle_eq {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    {R : ℝ} (hR : 0 ≤ R) (U V : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 3 * R < ‖x‖) :
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (radialObjectiveAt_admissible hM hN hR U).lipschitz (radialObjectiveAt_admissible hM hN hR U).weaklyConvex x =
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (radialObjectiveAt_admissible hM hN hR V).lipschitz (radialObjectiveAt_admissible hM hN hR V).weaklyConvex x := by
  apply fullOracle_congr_eventuallyEq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (radialObjectiveAt_eventuallyEq_outside (by omega) R U x hx).trans
    (radialObjectiveAt_eventuallyEq_outside (by omega) R V x hx).symm

end MP
