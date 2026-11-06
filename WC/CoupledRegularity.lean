import WC.Variational
import WC.RelaySmooth

/-!
# Blockwise grouping and coordinate monotonicity of the actual coupled function
-/

noncomputable section
namespace WC

open scoped BigOperators Classical

def nextWeight {M : ℕ} (w : EuclideanSpace ℝ (Fin M)) (m : Fin M) : ℝ :=
  if h : m.val + 1 < M then w ⟨m.val + 1, h⟩ else 0

def initialWeight {M : ℕ} (w : EuclideanSpace ℝ (Fin M)) : ℝ :=
  if h : 0 < M then w ⟨0, h⟩ else 0

def euclideanBlock {M N : ℕ} (x : ChainSpace M N) (m : Fin M) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (coupledBlock x m)

theorem nextWeight_nonneg {M : ℕ} {w : EuclideanSpace ℝ (Fin M)}
    (hw : w ∈ scoreWeights) (m : Fin M) : 0 ≤ nextWeight w m := by
  unfold nextWeight
  split_ifs
  · exact hw.1 _
  · rfl

theorem nextWeight_le_one {M : ℕ} {w : EuclideanSpace ℝ (Fin M)}
    (hw : w ∈ scoreWeights) (m : Fin M) : nextWeight w m ≤ 1 := by
  unfold nextWeight
  split_ifs
  · exact scoreWeights_coord_le_one hw _
  · norm_num

theorem nextWeight_castSucc {M : ℕ} (w : EuclideanSpace ℝ (Fin (M + 1))) (m : Fin M) :
    nextWeight w m.castSucc = w m.succ := by
  unfold nextWeight
  rw [dif_pos (show m.castSucc.val + 1 < M + 1 by simp)]
  rfl

@[simp] theorem nextWeight_last {M : ℕ} (w : EuclideanSpace ℝ (Fin (M + 1))) :
    nextWeight w (Fin.last M) = 0 := by simp [nextWeight]

/-- The activation sum with the terminal next-weight convention `w_(M+1)=0`. -/
theorem weighted_precedingGate_sum_generic {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    (∑ m, w m * precedingGate x m) =
      initialWeight w + ∑ m, nextWeight w m * currentBlockGate x m := by
  cases M with
  | zero => simp [initialWeight]
  | succ M =>
    have hsum : (∑ m : Fin (M + 1), nextWeight w m * currentBlockGate x m) =
        ∑ m : Fin M, w m.succ * currentBlockGate x m.castSucc := by
      rw [Fin.sum_univ_castSucc]
      simp only [nextWeight_castSucc, nextWeight_last, zero_mul, add_zero]
    rw [weighted_precedingGate_sum, hsum]
    simp [initialWeight]

/-- The precise block grouping used to prove monotonicity and weak convexity. -/
theorem weightedCoupledFunction_grouped {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    weightedCoupledFunction w x = 2 / (N : ℝ) *
      (initialWeight w + ∑ m,
        (w m * (tiltedBlock N (M * N) m.val (coupledBlock x m) - 5 / 4) +
          smoothBlockTerm (nextWeight w m) (euclideanBlock x m))) := by
  have hterm (m : Fin M) : smoothBlockTerm (nextWeight w m) (euclideanBlock x m) =
      nextWeight w m * currentBlockGate x m - 2 * blockProgress (coupledBlock x m) := rfl
  simp_rw [hterm]
  rw [weightedCoupledFunction_expansion, weighted_precedingGate_sum_generic]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem tiltedBlock_coordinate_antitone {N K m : ℕ} (u v : Fin N → ℝ)
    (huv : ∀ n, u n ≤ v n) : tiltedBlock N K m v ≤ tiltedBlock N K m u := by
  apply tiltedBlock_le (tiltedBlock_nonneg N K m u)
  intro n
  have h := fanPiece_le_tiltedBlock N K m u n
  have hc := mul_le_mul_of_nonneg_left (huv n) (show 0 ≤ (N : ℝ) / 8 by positivity)
  dsimp [fanPiece] at h ⊢
  linarith

theorem weightedCoupledFunction_coordinate_antitone {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (x y : ChainSpace M N) (hxy : ∀ i, x i ≤ y i) :
    weightedCoupledFunction w y ≤ weightedCoupledFunction w x := by
  rw [weightedCoupledFunction_grouped, weightedCoupledFunction_grouped]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro m _
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right
      (tiltedBlock_coordinate_antitone (coupledBlock x m) (coupledBlock y m)
        (fun n => hxy (m, n))) _) (hw.1 m)
  · exact antitone_smoothBlockTerm (nextWeight_nonneg hw m) (nextWeight_le_one hw m)
      (euclideanBlock x m) (euclideanBlock y m) (fun n => hxy (m, n))

/-- Coordinate monotonicity is proved for `f₀` itself via its attained maximum. -/
theorem coupledFunction_coordinate_antitone {M N : ℕ}
    (x y : ChainSpace M N) (hxy : ∀ i, x i ≤ y i) : coupledFunction y ≤ coupledFunction x := by
  rw [← weightedCoupledFunction_attains y]
  exact (weightedCoupledFunction_coordinate_antitone _ (positiveScoreOptimizer_mem _) x y hxy).trans
    (weightedCoupledFunction_le _ x (positiveScoreOptimizer_mem _))

end WC
