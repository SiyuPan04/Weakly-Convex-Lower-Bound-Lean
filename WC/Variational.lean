import WC.Construction
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

/-!
# Exact variational representation of the positive-score norm

This module constructs an optimizing nonnegative unit-ball vector explicitly,
including the zero-score case, and applies it to the actual coupled function.
-/

noncomputable section
namespace WC

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

def positiveScores (s : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => max (s i) 0)

def scoreWeights : Set (EuclideanSpace ℝ ι) := {w | (∀ i, 0 ≤ w i) ∧ ‖w‖ ≤ 1}

theorem scoreWeights_coord_le_one {w : EuclideanSpace ℝ ι} (hw : w ∈ scoreWeights) (i : ι) :
    w i ≤ 1 := by
  have hc := PiLp.norm_apply_le w i
  rw [Real.norm_eq_abs, abs_of_nonneg (hw.1 i)] at hc
  exact hc.trans hw.2

omit [Fintype ι] in
theorem positiveScores_nonneg (s : EuclideanSpace ℝ ι) (i : ι) :
    0 ≤ positiveScores s i := le_max_right _ _

theorem positiveScores_inner (s : EuclideanSpace ℝ ι) :
    inner ℝ (positiveScores s) s = ‖positiveScores s‖ ^ 2 := by
  rw [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.inner_apply, positiveScores, PiLp.toLp_apply]
  by_cases h : 0 ≤ s i
  · rw [max_eq_left h]
    ring
  · rw [max_eq_right (le_of_not_ge h)]
    ring

theorem positiveScore_dual_le (s : EuclideanSpace ℝ ι) {w : EuclideanSpace ℝ ι}
    (hw : w ∈ scoreWeights) : inner ℝ w s ≤ ‖positiveScores s‖ := by
  have hcoord : inner ℝ w s ≤ inner ℝ w (positiveScores s) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1 i)
  calc
    inner ℝ w s ≤ inner ℝ w (positiveScores s) := hcoord
    _ ≤ ‖w‖ * ‖positiveScores s‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖positiveScores s‖ :=
      mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)
    _ = ‖positiveScores s‖ := one_mul _

def positiveScoreOptimizer (s : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  if positiveScores s = 0 then 0 else ‖positiveScores s‖⁻¹ • positiveScores s

theorem positiveScoreOptimizer_mem (s : EuclideanSpace ℝ ι) :
    positiveScoreOptimizer s ∈ scoreWeights := by
  unfold positiveScoreOptimizer
  split_ifs with hp
  · constructor
    · intro i; simp
    · simp
  · have hn : 0 < ‖positiveScores s‖ := norm_pos_iff.mpr hp
    constructor
    · intro i
      simp only [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hn.le) (positiveScores_nonneg s i)
    · simp [norm_smul, hn.ne']

theorem positiveScoreOptimizer_attains (s : EuclideanSpace ℝ ι) :
    inner ℝ (positiveScoreOptimizer s) s = ‖positiveScores s‖ := by
  unfold positiveScoreOptimizer
  split_ifs with hp
  · simp [hp]
  · have hn : ‖positiveScores s‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    rw [real_inner_smul_left, positiveScores_inner]
    field_simp

theorem positiveScore_isGreatest (s : EuclideanSpace ℝ ι) :
    IsGreatest ((fun w => inner ℝ w s) '' scoreWeights) ‖positiveScores s‖ := by
  constructor
  · exact ⟨positiveScoreOptimizer s, positiveScoreOptimizer_mem s, positiveScoreOptimizer_attains s⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact positiveScore_dual_le s hw

theorem positiveScore_variational (s : EuclideanSpace ℝ ι) :
    sSup ((fun w => inner ℝ w s) '' scoreWeights) = ‖positiveScores s‖ :=
  (positiveScore_isGreatest s).csSup_eq

def coupledScores {M N : ℕ} (x : ChainSpace M N) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (coupledScore x)

/-- The weighted block expression `F_w` before reindexing the activation sum. -/
def weightedCoupledFunction {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (x : ChainSpace M N) : ℝ :=
  2 / (N : ℝ) * (inner ℝ w (coupledScores x) -
    2 * ∑ m, blockProgress (coupledBlock x m))

theorem positiveCoupledScores_eq {M N : ℕ} (x : ChainSpace M N) :
    positiveCoupledScores x = positiveScores (coupledScores x) := rfl

theorem weightedCoupledFunction_expansion {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    weightedCoupledFunction w x = 2 / (N : ℝ) *
      ((∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock x m)) +
       (∑ m, w m * precedingGate x m) - (5 / 4 : ℝ) * ∑ m, w m -
       2 * ∑ m, blockProgress (coupledBlock x m)) := by
  simp only [weightedCoupledFunction, coupledScores, PiLp.inner_apply, Real.inner_apply,
    coupledScore, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

def currentBlockGate {M N : ℕ} (x : ChainSpace M N) (m : Fin M) : ℝ :=
  progressGate ((4 * blockProgress (coupledBlock x m) - 1) / 3)

theorem precedingGate_succ {M N : ℕ} (x : ChainSpace (M + 1) N) (m : Fin M) :
    precedingGate x m.succ = currentBlockGate x m.castSucc := by
  unfold precedingGate currentBlockGate
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel]
  congr 2

/-- The activation sum shifts exactly one block, with the initial gate equal to one. -/
theorem weighted_precedingGate_sum {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin (M + 1))) (x : ChainSpace (M + 1) N) :
    (∑ m, w m * precedingGate x m) =
      w 0 + ∑ m : Fin M, w m.succ * currentBlockGate x m.castSucc := by
  rw [Fin.sum_univ_succ]
  simp only [precedingGate_succ]
  have hzero : precedingGate x 0 = 1 := by simp [precedingGate]
  rw [hzero, mul_one]

/-- The paper's relay expansion, with no activation term following the last block. -/
theorem weightedCoupledFunction_relay_expansion {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin (M + 1))) (x : ChainSpace (M + 1) N) :
    weightedCoupledFunction w x = 2 / (N : ℝ) *
      (w 0 + (∑ m, w m * (tiltedBlock N ((M + 1) * N) m.val
        (coupledBlock x m) - 5 / 4)) +
       (∑ m : Fin M, w m.succ * currentBlockGate x m.castSucc) -
       2 * ∑ m, blockProgress (coupledBlock x m)) := by
  rw [weightedCoupledFunction_expansion, weighted_precedingGate_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem weightedCoupledFunction_le {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) (hw : w ∈ scoreWeights) :
    weightedCoupledFunction w x ≤ coupledFunction x := by
  have h := positiveScore_dual_le (coupledScores x) hw
  unfold weightedCoupledFunction coupledFunction
  rw [positiveCoupledScores_eq]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (by positivity)

theorem weightedCoupledFunction_attains {M N : ℕ} (x : ChainSpace M N) :
    weightedCoupledFunction (positiveScoreOptimizer (coupledScores x)) x = coupledFunction x := by
  simp only [weightedCoupledFunction, positiveScoreOptimizer_attains,
    coupledFunction, positiveCoupledScores_eq]

/-- The actual coupled function is a maximum over the nonnegative Euclidean unit ball. -/
theorem coupledFunction_variational {M N : ℕ} (x : ChainSpace M N) :
    IsGreatest ((fun w => weightedCoupledFunction w x) '' scoreWeights) (coupledFunction x) := by
  constructor
  · exact ⟨positiveScoreOptimizer (coupledScores x), positiveScoreOptimizer_mem _,
      weightedCoupledFunction_attains x⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact weightedCoupledFunction_le w x hw

theorem coupledFunction_eq_sup {M N : ℕ} (x : ChainSpace M N) :
    coupledFunction x = sSup ((fun w => weightedCoupledFunction w x) '' scoreWeights) :=
  (coupledFunction_variational x).csSup_eq.symm

end WC
