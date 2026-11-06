import WC.ChainRadialBarrier
import WC.ChainWallGap
import WC.GeneralMoreauScaling
import WC.Numerics
import WC.RobustParameters

/-! The actual unit-normalized objective and its stationarity estimates.
The independent oracle-locality verification is used when assembling the
normalized rotated family. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E]

def normalizedChainWall {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E) : E → ℝ :=
  scaleFunction (1 / 2) (2 / 3) (liftedChainWall U)

def normalizedChainRadius (M N : ℕ) : ℝ := 6 * chainWallRadius M N

def normalizedChainTolerance (M N : ℕ) : ℝ := (3 / 2 : ℝ) * robustTolerance M N

theorem normalizedChainWall_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (normalizedChainWall U) := by
  have h := admissible_scale (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (liftedChainWall_admissible hM hN U)
  norm_num at h
  convert h using 1 <;> first | rfl | ring

theorem normalizedChainWall_moreau_gradient {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) :
    gradient (moreauEnvelope (1 / 2) (normalizedChainWall U)) x =
      (1 / 3 : ℝ) • gradient (moreauEnvelope (1 / 9) (liftedChainWall U)) ((2 / 3 : ℝ) • x) := by
  have hadm := liftedChainWall_admissible hM hN U
  have h := scaled_moreau_gradient (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) < 9 / 2) hadm.lipschitz hadm.weaklyConvex x
  norm_num at h
  exact h

theorem normalizedChainWall_moreau_gradient_norm {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) :
    ‖gradient (moreauEnvelope (1 / 2) (normalizedChainWall U)) x‖ =
      (1 / 3 : ℝ) * ‖gradient (moreauEnvelope (1 / 9) (liftedChainWall U)) ((2 / 3 : ℝ) • x)‖ := by
  rw [normalizedChainWall_moreau_gradient hM hN U x, norm_smul, Real.norm_eq_abs]
  norm_num

theorem normalizedChainWall_terminal_barrier {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, isometryProjection U ((2 / 3 : ℝ) • x) i ≤ 1 / (N : ℝ)) :
    1 / (32 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 2) (normalizedChainWall U)) x‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := liftedChainWall_moreau_barrier hM hN hMmax U ((2 / 3 : ℝ) • x) s hcard hsmall
  have hn := normalizedChainWall_moreau_gradient_norm hM hN U x
  have hscale : ‖gradient (moreauEnvelope (1 / 9) (liftedChainWall U)) ((2 / 3 : ℝ) • x)‖ =
      3 * ‖gradient (moreauEnvelope (1 / 2) (normalizedChainWall U)) x‖ := by linarith
  rw [hscale] at hb
  apply strict_barrier_from_square hNR (by positivity : 0 < 49 * (N : ℝ)) (le_refl _)
    (norm_nonneg _)
  have hdiv := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 9)
  convert hdiv using 1 <;> first | rfl | ring

theorem normalizedChainWall_exterior_gradient {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : normalizedChainRadius M N ≤ ‖x‖) :
    ‖gradient (moreauEnvelope (1 / 2) (normalizedChainWall U)) x‖ = 1 := by
  have hNpos : 0 < N := by omega
  have hLip := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hWC := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  have hdist : 4 * chainWallRadius M N ≤ ‖(2 / 3 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    dsimp [normalizedChainRadius] at hx
    linarith
  have hbase := radialWall_moreau_exterior hLip hWC (chainWallRadius_ge_one M N hN) hdist
  rw [normalizedChainWall_moreau_gradient_norm hM hN U x]
  change (1 / 3 : ℝ) * ‖gradient (moreauEnvelope (1 / 9)
    (radialWall (isometricLift U chainMajorant) (chainWallRadius M N))) ((2 / 3 : ℝ) • x)‖ = 1
  rw [hbase]
  norm_num

end WC
