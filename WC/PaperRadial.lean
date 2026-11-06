import WC.LogBandBudget
import WC.GeneralRadialBarrier
import WC.RobustLocality

/-! Literal logarithmic-band radius and actual Moreau barrier of
Lemma `newrand:wall`, alongside the safe enlarged radius of the main family. -/

noncomputable section
namespace WC

def paperInitialGap (M N : ℕ) : ℝ := (2 / (N : ℝ)) * (2 * (M : ℝ) + initialGamma M N)

theorem paperInitialGap_gapBound {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    GapBound (paperInitialGap M N) (chainMajorant (M := M) (N := N)) := by
  apply gapBound_iff_inf.mpr
  exact ⟨(chainMajorant_gapBound hM hN).bddBelow, (chainMajorant_gap hM hN).le⟩

def paperBandDimension (M N : ℕ) : ℝ := 25 * (N : ℝ) + 8 * (logarithmicBandCount M N : ℝ)

def paperWallRadius (M N : ℕ) : ℝ :=
  1 + ‖chainMinimizer M N‖ + paperInitialGap M N / 3 +
    96 * chainRadialConstant M N * paperBandDimension M N + 1 / 3

theorem paperWallRadius_ge_one {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) :
    1 ≤ paperWallRadius M N := by
  have hd := (paperInitialGap_gapBound hM hN).nonneg
  have hC := chainRadialConstant_nonneg M N hN
  have hD : 0 ≤ paperBandDimension M N := by unfold paperBandDimension; positivity
  have hp : 0 ≤ 96 * chainRadialConstant M N * paperBandDimension M N := by positivity
  unfold paperWallRadius
  linarith [norm_nonneg (chainMinimizer M N)]

theorem paperWallRadius_margin (M N : ℕ) :
    96 * chainRadialConstant M N * paperBandDimension M N ≤
      paperWallRadius M N - paperInitialGap M N / 3 := by
  unfold paperWallRadius
  linarith [norm_nonneg (chainMinimizer M N)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def paperChainWall {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E) : E → ℝ :=
  radialWall (isometricLift U chainMajorant) (paperWallRadius M N)

theorem paperChainWall_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    Admissible 3 (9 / 2) (paperInitialGap M N) (paperChainWall U) := by
  have hNpos : 0 < N := by omega
  have hl := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hw := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  exact ⟨radialWall_weaklyConvex (by norm_num) hw _, radialWall_lipschitz hl _,
    radialWall_gapBound (isometricLift_gap U (paperInitialGap_gapBound hM hN))
      (by have h := paperWallRadius_ge_one hM hN; linarith)⟩

theorem paperChainWall_minimizer {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    paperChainWall U (U (chainMinimizer M N)) = -(4 * (M : ℝ) / N) := by
  have hC := chainRadialConstant_nonneg M N hN
  have hD : 0 ≤ paperBandDimension M N := by unfold paperBandDimension; positivity
  have hp : 0 ≤ 96 * chainRadialConstant M N * paperBandDimension M N := by positivity
  have hR : ‖chainMinimizer M N‖ + paperInitialGap M N / 3 ≤ paperWallRadius M N := by
    unfold paperWallRadius
    linarith
  have hg := paperInitialGap_gapBound hM hN (chainMinimizer M N)
  rw [chainMajorant_minimizer (by omega : 0 < N)] at hg
  change max (chainMajorant (isometryProjection U (U (chainMinimizer M N))))
    (chainMajorant (isometryProjection U 0) + 3 * (‖U (chainMinimizer M N)‖ - paperWallRadius M N)) = _
  rw [isometryProjection_map, map_zero, U.norm_map, chainMajorant_minimizer (by omega : 0 < N)]
  apply max_eq_left
  linarith

theorem paperChainWall_infimum {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    sInf (Set.range (paperChainWall U)) = -(4 * (M : ℝ) / N) := by
  have hlower (x : E) : -(4 * (M : ℝ) / N) ≤ paperChainWall U x :=
    (chainMajorant_lower_bound (by omega : 0 < N) (isometryProjection U x)).trans (le_max_left _ _)
  have hb : BddBelow (Set.range (paperChainWall U)) := by
    refine ⟨-(4 * (M : ℝ) / N), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hlower x
  apply le_antisymm
  · have h := csInf_le hb (Set.mem_range_self (U (chainMinimizer M N)))
    rwa [paperChainWall_minimizer hM hN U] at h
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hlower x)

theorem paperChainWall_exact_gap {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    paperChainWall U 0 - sInf (Set.range (paperChainWall U)) = paperInitialGap M N := by
  have hz : paperChainWall U 0 = chainMajorant (0 : ChainSpace M N) := by
    change max (chainMajorant (isometryProjection U 0))
      (chainMajorant (isometryProjection U 0) + 3 * (‖(0 : E)‖ - paperWallRadius M N)) = _
    simp only [map_zero, norm_zero]
    apply max_eq_left
    have h := paperWallRadius_ge_one hM hN
    linarith
  rw [hz, paperChainWall_infimum hM hN U, ← chainMajorant_infimum (by omega : 0 < N)]
  exact chainMajorant_gap hM hN

variable [ProperSpace E] [FiniteDimensional ℝ E]

theorem paperChainWall_moreau_barrier {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, isometryProjection U x i ≤ robustTolerance M N) :
    (15 / 16 : ℝ) / paperBandDimension M N ≤
      ‖gradient (moreauEnvelope (1 / 9) (paperChainWall U)) x‖ ^ 2 := by
  apply chainRadialWall_moreau_barrier hN (paperWallRadius_ge_one hM hN)
    (paperInitialGap_gapBound hM hN) (chain_source_radius_logarithmic_coverage hM hN)
    (paperWallRadius_margin M N) U x s hcard
  intro i hi
  exact (hsmall i hi).trans (robustTolerance_le_inv_N M (by omega))

theorem paperChainWall_moreau_exterior {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 4 * paperWallRadius M N ≤ ‖x‖) :
    ‖gradient (moreauEnvelope (1 / 9) (paperChainWall U)) x‖ = 3 :=
  radialWall_moreau_exterior (isometricLift_lipschitz U (by norm_num) (chainMajorant_lipschitz (by omega)))
    (isometricLift_weaklyConvex U (by norm_num) (chainMajorant_weaklyConvex (by omega)))
    (paperWallRadius_ge_one hM hN) hx

end WC
