import WC.Block
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The actual coupled function from Section 4, with zero-based block indices. -/

noncomputable section

namespace WC

open scoped BigOperators Classical

abbrev ChainSpace (M N : ℕ) := EuclideanSpace ℝ (Fin M × Fin N)

def coupledBlock {M N : ℕ} (x : ChainSpace M N) (m : Fin M) : Fin N → ℝ :=
  fun n => x (m, n)

def precedingGate {M N : ℕ} (x : ChainSpace M N) (m : Fin M) : ℝ :=
  if m.val = 0 then 1 else
    progressGate ((4 * blockProgress (coupledBlock x
      ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.isLt⟩) - 1) / 3)

def coupledScore {M N : ℕ} (x : ChainSpace M N) (m : Fin M) : ℝ :=
  tiltedBlock N (M * N) m.val (coupledBlock x m) + precedingGate x m - 5 / 4

def positiveCoupledScores {M N : ℕ} (x : ChainSpace M N) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (fun m => max (coupledScore x m) 0)

/-- The manuscript's function `f₀`, before taking a Lipschitz majorant. -/
def coupledFunction {M N : ℕ} (x : ChainSpace M N) : ℝ :=
  2 / (N : ℝ) * (‖positiveCoupledScores x‖ - 2 * ∑ m, blockProgress (coupledBlock x m))

theorem precedingGate_nonneg {M N : ℕ} (x : ChainSpace M N) (m : Fin M) :
    0 ≤ precedingGate x m := by
  unfold precedingGate
  split_ifs
  · norm_num
  · exact progressGate_nonneg _

theorem precedingGate_le_one {M N : ℕ} (x : ChainSpace M N) (m : Fin M) :
    precedingGate x m ≤ 1 := by
  unfold precedingGate
  split_ifs
  · rfl
  · exact progressGate_le_one _

/-- The lower bound `m₀ = -4M/N` is for the actual constructed function. -/
theorem coupledFunction_lower_bound {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    -(4 * (M : ℝ) / N) ≤ coupledFunction x := by
  have hs : (∑ m : Fin M, blockProgress (coupledBlock x m)) ≤ M := by
    calc
      _ ≤ ∑ _ : Fin M, (1 : ℝ) := Finset.sum_le_sum fun m _ => blockProgress_le_one hN _
      _ = M := by simp
  have hn := norm_nonneg (positiveCoupledScores x)
  have hi : -(2 * (M : ℝ)) ≤
      ‖positiveCoupledScores x‖ - 2 * ∑ m, blockProgress (coupledBlock x m) := by linarith
  unfold coupledFunction
  calc
    -(4 * (M : ℝ) / N) = (2 / (N : ℝ)) * (-(2 * (M : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

theorem coupledFunction_bddBelow {M N : ℕ} (hN : 0 < N) :
    BddBelow (Set.range (coupledFunction (M := M) (N := N))) := by
  refine ⟨-(4 * (M : ℝ) / N), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact coupledFunction_lower_bound hN x

@[simp] theorem coupledBlock_zero {M N : ℕ} (m : Fin M) :
    coupledBlock (0 : ChainSpace M N) m = 0 := by
  funext n
  rfl

@[simp] theorem blockProgress_zero_fun (N : ℕ) : blockProgress (0 : Fin N → ℝ) = 0 :=
  blockProgress_zero N

@[simp] theorem precedingGate_zero {M N : ℕ} (m : Fin M) :
    precedingGate (0 : ChainSpace M N) m = if m.val = 0 then 1 else 0 := by
  unfold precedingGate
  split_ifs with hm
  · rfl
  · rw [coupledBlock_zero, blockProgress_zero_fun]
    norm_num [progressGate]

theorem tiltedBlock_zero_eq_first {N K m : ℕ} (hN : 0 < N) (hm : m * N < K) :
    tiltedBlock N K m (fun _ => 0) = tiltIntercept K (m * N) := by
  let n0 : Fin N := ⟨0, hN⟩
  apply le_antisymm
  · apply tiltedBlock_le (le_of_lt (lt_trans (by norm_num) (tiltIntercept_gt_one hm)))
    intro n
    simp only [fanPiece, mul_zero, sub_zero]
    by_cases hn : n.val = 0
    · simp [hn]
    · exact le_of_lt (tiltIntercept_strictAnti (Nat.add_lt_add_left (Nat.pos_of_ne_zero hn) _))
  · have h := fanPiece_le_tiltedBlock N K m (fun _ => 0) n0
    simpa [fanPiece, n0] using h

theorem coupledScore_zero {M N : ℕ} (hN : 0 < N) (m : Fin M) :
    coupledScore (0 : ChainSpace M N) m =
      tiltIntercept (M * N) (m.val * N) + (if m.val = 0 then 1 else 0) - 5 / 4 := by
  unfold coupledScore
  rw [coupledBlock_zero, precedingGate_zero]
  exact congrArg (fun t : ℝ => t + (if m.val = 0 then 1 else 0) - 5 / 4)
    (tiltedBlock_zero_eq_first hN (Nat.mul_lt_mul_of_pos_right m.isLt hN))

theorem noninitial_coupledScore_zero_neg {M N : ℕ} (hN : 0 < N) (m : Fin M)
    (hm : m.val ≠ 0) : coupledScore (0 : ChainSpace M N) m < -(7 / 32) := by
  rw [coupledScore_zero hN m, if_neg hm]
  have h := tiltIntercept_lt (K := M * N) (r := m.val * N)
  linarith

/-- The scalar `γ` in the initial-gap formula. -/
def initialGamma (M N : ℕ) : ℝ := tiltIntercept (M * N) 0 - 1 / 4

theorem initialGamma_bounds {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    3 / 4 < initialGamma M N ∧ initialGamma M N < 13 / 16 := by
  have hlo := tiltIntercept_gt_one (Nat.mul_pos hM hN)
  have hhi := tiltIntercept_lt (K := M * N) (r := 0)
  unfold initialGamma
  constructor <;> linarith

theorem positiveCoupledScores_zero {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    positiveCoupledScores (0 : ChainSpace M N) =
      EuclideanSpace.single ⟨0, hM⟩ (initialGamma M N) := by
  apply PiLp.ext
  intro m
  by_cases hm : m.val = 0
  · have heq : m = ⟨0, hM⟩ := Fin.ext hm
    subst m
    have hg := (initialGamma_bounds hM hN).1
    have hscore : coupledScore (0 : ChainSpace M N) ⟨0, hM⟩ = initialGamma M N := by
      rw [coupledScore_zero hN]
      norm_num [initialGamma]
      ring
    simp only [positiveCoupledScores, PiLp.toLp_apply]
    rw [hscore, max_eq_left (show 0 ≤ initialGamma M N by linarith)]
    simp
  · have heq : m ≠ ⟨0, hM⟩ := fun h => hm (congrArg Fin.val h)
    have hneg := noninitial_coupledScore_zero_neg hN m hm
    simp only [positiveCoupledScores, PiLp.toLp_apply]
    rw [max_eq_right (by linarith)]
    simp [heq]

theorem coupledFunction_zero {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    coupledFunction (0 : ChainSpace M N) = 2 * initialGamma M N / N := by
  unfold coupledFunction
  rw [positiveCoupledScores_zero hM hN]
  have hg : 0 ≤ initialGamma M N := by have h := (initialGamma_bounds hM hN).1; linarith
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hg,
    coupledBlock_zero, blockProgress_zero_fun, Finset.sum_const_zero, mul_zero, sub_zero]
  ring

/-- A point where all blocks are complete, before the majorant is taken. -/
def constantCompletion (M N : ℕ) : ChainSpace M N :=
  WithLp.toLp 2 (fun _ => 9 / (N : ℝ))

theorem blockProgress_completion {N : ℕ} (hN : 0 < N) :
    blockProgress (fun _ : Fin N => 9 / (N : ℝ)) = 1 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have heq : (N : ℝ) / 4 * (9 / (N : ℝ)) = 9 / 4 := by field_simp
  have htheta : 1 / (64 * (N : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * (N : ℝ))).mpr
    nlinarith
  have harg : 1 ≤ (N : ℝ) / 4 * (9 / (N : ℝ)) - 1 / (64 * (N : ℝ)) := by
    rw [heq]
    linarith
  unfold blockProgress
  simp only [progressGate_of_one_le harg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (ne_of_gt hpos)

theorem tiltedBlock_completion {N K m : ℕ} (hN : 0 < N) :
    tiltedBlock N K m (fun _ => 9 / (N : ℝ)) = 0 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (N : ℝ) / 8 * (9 / (N : ℝ)) = 9 / 8 := by field_simp
  apply le_antisymm
  · apply tiltedBlock_le le_rfl
    intro n
    simp only [fanPiece, heq]
    have h := tiltIntercept_lt (K := K) (r := m * N + n.val)
    linarith
  · exact tiltedBlock_nonneg N K m _

theorem coupledFunction_completion {M N : ℕ} (hN : 0 < N) :
    coupledFunction (constantCompletion M N) = -(4 * (M : ℝ) / N) := by
  have hblocks : ∀ m : Fin M, coupledBlock (constantCompletion M N) m =
      fun _ => 9 / (N : ℝ) := fun _ => rfl
  have hgates : ∀ m : Fin M, precedingGate (constantCompletion M N) m = 1 := by
    intro m
    unfold precedingGate
    split_ifs
    · rfl
    · rw [hblocks, blockProgress_completion hN]
      norm_num
  have hscores : ∀ m : Fin M, coupledScore (constantCompletion M N) m = -(1 / 4) := by
    intro m
    unfold coupledScore
    rw [hblocks, tiltedBlock_completion hN, hgates]
    norm_num
  have hp : positiveCoupledScores (constantCompletion M N) = 0 := by
    apply PiLp.ext
    intro m
    simp [positiveCoupledScores, hscores]
  unfold coupledFunction
  rw [hp]
  simp only [norm_zero, hblocks, blockProgress_completion hN, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- The exact minimum of the raw function is attained at the displayed point. -/
theorem coupledFunction_infimum {M N : ℕ} (hN : 0 < N) :
    sInf (Set.range (coupledFunction (M := M) (N := N))) = -(4 * (M : ℝ) / N) := by
  apply le_antisymm
  · have h := csInf_le (coupledFunction_bddBelow hN)
      (Set.mem_range_self (constantCompletion M N))
    simpa only [coupledFunction_completion hN] using h
  · exact le_csInf (Set.range_nonempty _) (by
      rintro _ ⟨x, rfl⟩
      exact coupledFunction_lower_bound hN x)

theorem coupledFunction_gap {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    coupledFunction (0 : ChainSpace M N) - sInf (Set.range (coupledFunction (M := M) (N := N))) =
      (2 / (N : ℝ)) * (2 * (M : ℝ) + initialGamma M N) := by
  rw [coupledFunction_zero hM hN, coupledFunction_infimum hN]
  ring

/-- The positive part of `(9/N)·1 - x`, used in the majorant growth estimate. -/
def positiveDeficit {M N : ℕ} (x : ChainSpace M N) : ChainSpace M N :=
  WithLp.toLp 2 (fun i => max (9 / (N : ℝ) - x i) 0)

def positiveBlockDeficit {M N : ℕ} (x : ChainSpace M N) (m : Fin M) :
    EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun n => positiveDeficit x (m, n))

theorem blockFan_le_deficit_norm {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) (m : Fin M) :
    tiltedBlock N (M * N) m.val (coupledBlock x m) ≤
      (N : ℝ) / 8 * ‖positiveBlockDeficit x m‖ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ (N : ℝ) / 8 := by positivity
  have heq : (N : ℝ) / 8 * (9 / (N : ℝ)) = 9 / 8 := by field_simp
  apply tiltedBlock_le (mul_nonneg ha (norm_nonneg _))
  intro n
  have hcoord : max (9 / (N : ℝ) - x (m, n)) 0 ≤ ‖positiveBlockDeficit x m‖ := by
    have h := PiLp.norm_apply_le (positiveBlockDeficit x m) n
    change ‖max (9 / (N : ℝ) - x (m, n)) 0‖ ≤ ‖positiveBlockDeficit x m‖ at h
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (9 / (N : ℝ) - x (m, n)) 0)] at h
    exact h
  have hintercept : tiltIntercept (M * N) (m.val * N + n.val) ≤ 9 / 8 := by
    have h := tiltIntercept_lt (K := M * N) (r := m.val * N + n.val)
    linarith
  have hdef := le_max_left (9 / (N : ℝ) - x (m, n)) (0 : ℝ)
  have hcoord' := mul_le_mul_of_nonneg_left hcoord ha
  have hdef' := mul_le_mul_of_nonneg_left hdef ha
  unfold fanPiece coupledBlock
  nlinarith [heq]

theorem positiveCoupledScore_le_deficit {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (m : Fin M) :
    max (coupledScore x m) 0 ≤ (N : ℝ) / 8 * ‖positiveBlockDeficit x m‖ := by
  apply max_le
  · have hfan := blockFan_le_deficit_norm hN x m
    have hgate := precedingGate_le_one x m
    unfold coupledScore
    linarith
  · positivity

theorem sum_blockDeficit_norm_sq {M N : ℕ} (x : ChainSpace M N) :
    (∑ m, ‖positiveBlockDeficit x m‖ ^ 2) = ‖positiveDeficit x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, positiveBlockDeficit]
  exact (Fintype.sum_prod_type (fun i : Fin M × Fin N => positiveDeficit x i ^ 2)).symm

theorem positiveCoupledScores_norm_le {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    ‖positiveCoupledScores x‖ ≤ (N : ℝ) / 8 * ‖positiveDeficit x‖ := by
  have hs : ‖positiveCoupledScores x‖ ^ 2 ≤
      ((N : ℝ) / 8) ^ 2 * ‖positiveDeficit x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← sum_blockDeficit_norm_sq x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    have hbound := positiveCoupledScore_le_deficit hN x m
    have hsq := sq_le_sq₀ (le_max_right (coupledScore x m) 0)
      (show 0 ≤ (N : ℝ) / 8 * ‖positiveBlockDeficit x m‖ by positivity)
    have h := hsq.mpr hbound
    simpa only [positiveCoupledScores, PiLp.toLp_apply, mul_pow] using h
  have hright : 0 ≤ (N : ℝ) / 8 * ‖positiveDeficit x‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  simpa only [mul_pow] using hs

/-- Equation `newrand:growth`, proved for the explicit raw coupled function. -/
theorem coupledFunction_growth {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    coupledFunction x ≤ (1 / 4 : ℝ) * ‖positiveDeficit x‖ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hscore := positiveCoupledScores_norm_le hN x
  have hs : 0 ≤ ∑ m, blockProgress (coupledBlock x m) :=
    Finset.sum_nonneg fun m _ => blockProgress_nonneg _
  unfold coupledFunction
  calc
    _ ≤ (2 / (N : ℝ)) * ((N : ℝ) / 8 * ‖positiveDeficit x‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (1 / 4 : ℝ) * ‖positiveDeficit x‖ := by field_simp <;> ring

end WC
