import WC.WeightShift
import WC.CoupledCurvature

/-! The dimension-independent Lipschitz bound for the positive-score term. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem euclideanTiltedBlock_oneSided (N K m : ℕ) (x y : EuclideanSpace ℝ (Fin N)) :
    euclideanTiltedBlock N K m x ≤ euclideanTiltedBlock N K m y +
      (N : ℝ) / 8 * ‖x - y‖ := by
  have ha : 0 ≤ (N : ℝ) / 8 := by positivity
  apply tiltedBlock_le
  · exact add_nonneg (tiltedBlock_nonneg N K m _) (mul_nonneg ha (norm_nonneg _))
  intro n
  have hc := PiLp.norm_apply_le (x - y) n
  change ‖x n - y n‖ ≤ ‖x - y‖ at hc
  rw [Real.norm_eq_abs] at hc
  have hcoord := mul_le_mul_of_nonneg_left ((neg_le_abs (x n - y n)).trans hc) ha
  have hp := fanPiece_le_tiltedBlock N K m (fun i => y i) n
  dsimp [fanPiece, euclideanTiltedBlock] at hp ⊢
  nlinarith

theorem euclideanTiltedBlock_abs_sub_le (N K m : ℕ) (x y : EuclideanSpace ℝ (Fin N)) :
    |euclideanTiltedBlock N K m x - euclideanTiltedBlock N K m y| ≤
      (N : ℝ) / 8 * ‖x - y‖ := by
  have hx := euclideanTiltedBlock_oneSided N K m x y
  have hy := euclideanTiltedBlock_oneSided N K m y x
  rw [norm_sub_rev] at hy
  apply abs_le.mpr
  constructor <;> linarith

def blockNorms {M N : ℕ} (x : ChainSpace M N) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (fun m => ‖euclideanBlock x m‖)

theorem blockNorms_norm {M N : ℕ} (x : ChainSpace M N) : ‖blockNorms x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  exact sum_euclideanBlock_norm_sq x

theorem weighted_blockNorm_sum_le {M N : ℕ} {w : EuclideanSpace ℝ (Fin M)}
    (hw : w ∈ scoreWeights) (z : ChainSpace M N) :
    (∑ m, w m * ‖euclideanBlock z m‖) ≤ ‖z‖ := by
  have hinner : (∑ m, w m * ‖euclideanBlock z m‖) = inner ℝ w (blockNorms z) := by
    simp only [PiLp.inner_apply, Real.inner_apply, blockNorms]
  rw [hinner]
  calc
    _ ≤ ‖w‖ * ‖blockNorms z‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖blockNorms z‖ := mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)
    _ = ‖z‖ := by rw [one_mul, blockNorms_norm]

theorem weighted_sum_abs_sub_le {M N : ℕ} {w : EuclideanSpace ℝ (Fin M)}
    (hw : w ∈ scoreWeights) {C : ℝ} (hC : 0 ≤ C) (x y : ChainSpace M N)
    (a b : Fin M → ℝ)
    (hbound : ∀ m, |a m - b m| ≤ C * ‖euclideanBlock (x - y) m‖) :
    |(∑ m, w m * a m) - ∑ m, w m * b m| ≤ C * ‖x - y‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m, |w m * a m - w m * b m| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m, w m * |a m - b m| := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 m)]
    _ ≤ ∑ m, w m * (C * ‖euclideanBlock (x - y) m‖) :=
      Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hbound m) (hw.1 m)
    _ = C * ∑ m, w m * ‖euclideanBlock (x - y) m‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_left (weighted_blockNorm_sum_le hw (x - y)) hC

theorem currentBlockGate_abs_sub_le {M N : ℕ} (hN : 0 < N)
    (x y : ChainSpace M N) (m : Fin M) :
    |currentBlockGate x m - currentBlockGate y m| ≤
      (3 * Real.sqrt (N : ℝ) / 4) * ‖euclideanBlock (x - y) m‖ := by
  have hrelay := relayProgress_abs_sub_le (euclideanProgress (euclideanBlock x m))
    (euclideanProgress (euclideanBlock y m))
  have hprog := euclideanProgress_abs_sub_le hN (euclideanBlock x m) (euclideanBlock y m)
  change |currentBlockGate x m - currentBlockGate y m| ≤
    2 * |euclideanProgress (euclideanBlock x m) - euclideanProgress (euclideanBlock y m)| at hrelay
  have h := hrelay.trans (mul_le_mul_of_nonneg_left hprog (by norm_num))
  have heq : euclideanBlock (x - y) m = euclideanBlock x m - euclideanBlock y m := by
    apply PiLp.ext
    intro n
    rfl
  rw [heq]
  convert h using 1 <;> first | rfl | ring

theorem coupledScores_inner_abs_sub_le {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (x y : ChainSpace M N) :
    |inner ℝ w (coupledScores x) - inner ℝ w (coupledScores y)| ≤
      ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) * ‖x - y‖ := by
  have hfan := weighted_sum_abs_sub_le hw (show 0 ≤ (N : ℝ) / 8 by positivity) x y
    (fun m => tiltedBlock N (M * N) m.val (coupledBlock x m))
    (fun m => tiltedBlock N (M * N) m.val (coupledBlock y m)) (fun m => by
      exact euclideanTiltedBlock_abs_sub_le N (M * N) m.val (euclideanBlock x m) (euclideanBlock y m))
  have hgate := weighted_sum_abs_sub_le (nextWeights_mem_scoreWeights hw)
    (show 0 ≤ 3 * Real.sqrt (N : ℝ) / 4 by positivity) x y
    (currentBlockGate x) (currentBlockGate y) (currentBlockGate_abs_sub_le hN x y)
  have hexp (z : ChainSpace M N) : inner ℝ w (coupledScores z) =
      (∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock z m)) +
      initialWeight w + (∑ m, nextWeight w m * currentBlockGate z m) -
      (5 / 4 : ℝ) * ∑ m, w m := by
    simp only [coupledScores, PiLp.inner_apply, Real.inner_apply, coupledScore, mul_sub, mul_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [weighted_precedingGate_sum_generic]
    ring
  rw [hexp x, hexp y]
  have heq :
      ((∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock x m)) + initialWeight w +
        (∑ m, nextWeight w m * currentBlockGate x m) - (5 / 4 : ℝ) * ∑ m, w m) -
      ((∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock y m)) + initialWeight w +
        (∑ m, nextWeight w m * currentBlockGate y m) - (5 / 4 : ℝ) * ∑ m, w m) =
      ((∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock x m)) -
        ∑ m, w m * tiltedBlock N (M * N) m.val (coupledBlock y m)) +
      ((∑ m, nextWeight w m * currentBlockGate x m) - ∑ m, nextWeight w m * currentBlockGate y m) := by ring
  rw [heq]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (N : ℝ) / 8 * ‖x - y‖ + (3 * Real.sqrt (N : ℝ) / 4) * ‖x - y‖ :=
      add_le_add hfan hgate
    _ = _ := by ring

theorem positiveCoupledScores_norm_abs_sub_le {M N : ℕ} (hN : 0 < N)
    (x y : ChainSpace M N) :
    |‖positiveCoupledScores x‖ - ‖positiveCoupledScores y‖| ≤
      ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) * ‖x - y‖ := by
  have hone (x y : ChainSpace M N) :
      ‖positiveCoupledScores x‖ - ‖positiveCoupledScores y‖ ≤
        ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) * ‖x - y‖ := by
    let w := positiveScoreOptimizer (coupledScores x)
    have hw : w ∈ scoreWeights := positiveScoreOptimizer_mem _
    have hx := positiveScoreOptimizer_attains (coupledScores x)
    have hy := positiveScore_dual_le (coupledScores y) hw
    have h := coupledScores_inner_abs_sub_le hN w hw x y
    have hl := le_trans (le_abs_self _) h
    change inner ℝ w (coupledScores x) = ‖positiveCoupledScores x‖ at hx
    change inner ℝ w (coupledScores y) ≤ ‖positiveCoupledScores y‖ at hy
    linarith
  have hx := hone x y
  have hy := hone y x
  rw [norm_sub_rev] at hy
  apply abs_le.mpr
  constructor <;> linarith

def positiveScoreTerm {M N : ℕ} (x : ChainSpace M N) : ℝ :=
  2 / (N : ℝ) * ‖positiveCoupledScores x‖

/-- The precise `c_N` Lipschitz certificate in Proposition `prop:regularity`. -/
theorem positiveScoreTerm_lipschitz {M N : ℕ} (hN : 0 < N) :
    GloballyLipschitz (1 / 4 + 3 / (2 * Real.sqrt (N : ℝ)))
      (positiveScoreTerm (M := M) (N := N)) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hpos
  have hconst : (2 / (N : ℝ)) * ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) =
      1 / 4 + 3 / (2 * Real.sqrt (N : ℝ)) := by
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)]
  intro x y
  unfold positiveScoreTerm
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 2 / (N : ℝ) by positivity)]
  calc
    _ ≤ (2 / (N : ℝ)) * (((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (positiveCoupledScores_norm_abs_sub_le hN x y) (by positivity)
    _ = _ := by rw [← mul_assoc, hconst]

theorem positiveScoreTerm_lipschitzConstant_le {N : ℕ} (hN : 256 ≤ N) :
    1 / 4 + 3 / (2 * Real.sqrt (N : ℝ)) ≤ 11 / 32 := by
  have hs : (16 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc
      (16 : ℝ) = Real.sqrt 256 := by
        rw [← show (16 : ℝ) ^ 2 = 256 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hd : 0 < 2 * Real.sqrt (N : ℝ) := by linarith
  have hf : 3 / (2 * Real.sqrt (N : ℝ)) ≤ 3 / 32 :=
    (div_le_iff₀ hd).mpr (by linarith)
  linarith

theorem positiveScoreTerm_lipschitz_uniform {M N : ℕ} (hN : 256 ≤ N) :
    GloballyLipschitz (11 / 32 : ℝ) (positiveScoreTerm (M := M) (N := N)) := by
  have hpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  intro x y
  exact (positiveScoreTerm_lipschitz hpos x y).trans
    (mul_le_mul_of_nonneg_right (positiveScoreTerm_lipschitzConstant_le hN) (norm_nonneg _))

end WC
