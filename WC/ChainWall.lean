import WC.RadialExterior
import WC.RadialInnerBound
import WC.ChainBandBudget
import WC.InitialGap
import WC.Isometry

/-! The concrete large-radius wall, its true regularity and initial gap.
We use the admissible maximum of `3N` source bands; increasing the radius
does not change the initial gap or the eventual normalized constants. -/

noncomputable section
namespace WC

theorem chainMajorant_gapBound {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    GapBound (6 * (M : ℝ) / N) (chainMajorant (M := M) (N := N)) := by
  apply gapBound_iff_inf.mpr
  exact ⟨⟨-(4 * (M : ℝ) / N), by
    rintro _ ⟨x, rfl⟩
    exact chainMajorant_lower_bound (by omega) x⟩, chainMajorant_gap_le hM hN⟩

theorem chainRadialConstant_nonneg (M N : ℕ) (hN : 256 ≤ N) :
    0 ≤ chainRadialConstant M N := by
  have hr := chain_source_radius_nonneg M N hN
  unfold chainRadialConstant
  positivity

def chainWallRadius (M N : ℕ) : ℝ :=
  1 + ‖chainMinimizer M N‖ + (6 * (M : ℝ) / N) / 3 +
    96 * chainRadialConstant M N * (49 * (N : ℝ)) + 1 / 3

theorem chainWallRadius_ge_one (M N : ℕ) (hN : 256 ≤ N) : 1 ≤ chainWallRadius M N := by
  have hC := chainRadialConstant_nonneg M N hN
  unfold chainWallRadius
  have hgap : 0 ≤ (6 * (M : ℝ) / N) / 3 := by positivity
  have hprod : 0 ≤ 96 * chainRadialConstant M N * (49 * (N : ℝ)) := by positivity
  linarith [norm_nonneg (chainMinimizer M N)]

theorem chainWallRadius_margin (M N : ℕ) (hN : 256 ≤ N) :
    96 * chainRadialConstant M N * (49 * (N : ℝ)) <
      chainWallRadius M N - (6 * (M : ℝ) / N) / 3 := by
  unfold chainWallRadius
  linarith [norm_nonneg (chainMinimizer M N)]

theorem radialWall_gapBound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {Δ R : ℝ} (hgap : GapBound Δ f) (hR : 0 ≤ R) :
    GapBound Δ (radialWall f R) := by
  intro x
  have hzero : radialWall f R 0 = f 0 := by
    apply max_eq_left
    simp only [radialBranch, norm_zero]
    linarith
  rw [hzero]
  exact (sub_le_sub_left (le_max_left (f x) (radialBranch f R x)) (f 0)).trans (hgap x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def liftedChainWall {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E) : E → ℝ :=
  radialWall (isometricLift U chainMajorant) (chainWallRadius M N)

theorem liftedChainWall_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    Admissible 3 (9 / 2) (6 * (M : ℝ) / N) (liftedChainWall U) := by
  have hNpos : 0 < N := by omega
  have hLip := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hWC := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  exact ⟨radialWall_weaklyConvex (by norm_num) hWC _, radialWall_lipschitz hLip _,
    radialWall_gapBound (isometricLift_gap U (chainMajorant_gapBound hM hN))
      (le_trans (by norm_num) (chainWallRadius_ge_one M N hN))⟩

end WC
