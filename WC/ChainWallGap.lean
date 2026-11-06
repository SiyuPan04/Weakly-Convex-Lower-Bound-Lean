import WC.ChainWall

/-! The concrete radial modification preserves the exact initial gap. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem liftedChainWall_zero {M N : ℕ} (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    liftedChainWall U 0 = chainMajorant (0 : ChainSpace M N) := by
  change max (chainMajorant (isometryProjection U 0))
    (chainMajorant (isometryProjection U 0) + 3 * (‖(0 : E)‖ - chainWallRadius M N)) = _
  simp only [map_zero, norm_zero]
  apply max_eq_left
  have hR := chainWallRadius_ge_one M N hN
  linarith

theorem liftedChainWall_minimizer {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    liftedChainWall U (U (chainMinimizer M N)) = -(4 * (M : ℝ) / N) := by
  have hNpos : 0 < N := by omega
  have hC := chainRadialConstant_nonneg M N hN
  have hprod : 0 ≤ 96 * chainRadialConstant M N * (49 * (N : ℝ)) := by positivity
  have hR : ‖chainMinimizer M N‖ + (6 * (M : ℝ) / N) / 3 ≤ chainWallRadius M N := by
    unfold chainWallRadius
    linarith
  have hgap := chainMajorant_gapBound hM hN (chainMinimizer M N)
  rw [chainMajorant_minimizer hNpos] at hgap
  change max (chainMajorant (isometryProjection U (U (chainMinimizer M N))))
    (chainMajorant (isometryProjection U 0) + 3 * (‖U (chainMinimizer M N)‖ - chainWallRadius M N)) = _
  rw [isometryProjection_map, map_zero, U.norm_map, chainMajorant_minimizer hNpos]
  apply max_eq_left
  linarith

theorem liftedChainWall_infimum {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    sInf (Set.range (liftedChainWall U)) = -(4 * (M : ℝ) / N) := by
  have hlower (x : E) : -(4 * (M : ℝ) / N) ≤ liftedChainWall U x :=
    (chainMajorant_lower_bound (by omega : 0 < N) (isometryProjection U x)).trans
      (le_max_left _ _)
  have hb : BddBelow (Set.range (liftedChainWall U)) := by
    refine ⟨-(4 * (M : ℝ) / N), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hlower x
  apply le_antisymm
  · have h := csInf_le hb (Set.mem_range_self (U (chainMinimizer M N)))
    rwa [liftedChainWall_minimizer hM hN U] at h
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hlower x)

theorem liftedChainWall_exact_gap {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    liftedChainWall U 0 - sInf (Set.range (liftedChainWall U)) =
      (2 / (N : ℝ)) * (2 * (M : ℝ) + initialGamma M N) := by
  rw [liftedChainWall_zero hN U, liftedChainWall_infimum hM hN U,
    ← chainMajorant_infimum (by omega : 0 < N)]
  exact chainMajorant_gap hM hN

end WC
