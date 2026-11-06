import WC.ChainMajorant

/-! A finite global Lipschitz constant for the raw construction, and the
uniform source radius used in the full majorant maximum rule. -/

noncomputable section
namespace WC

open scoped BigOperators

def progressReward {M N : ℕ} (x : ChainSpace M N) : ℝ :=
  4 / (N : ℝ) * ∑ m, blockProgress (coupledBlock x m)

def rawLipschitzConstant (M N : ℕ) : ℝ :=
  (1 / 4 + 3 / (2 * Real.sqrt N)) +
    (4 / (N : ℝ)) * (M : ℝ) * (3 * Real.sqrt N / 8)

theorem coupledFunction_eq_score_sub_reward {M N : ℕ} (x : ChainSpace M N) :
    coupledFunction x = positiveScoreTerm x - progressReward x := by
  dsimp [coupledFunction, positiveScoreTerm, progressReward]
  ring

theorem progressReward_range {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    0 ≤ progressReward x ∧ progressReward x ≤ 4 * (M : ℝ) / N := by
  have hc : 0 ≤ 4 / (N : ℝ) := by positivity
  have hs0 : 0 ≤ ∑ m, blockProgress (coupledBlock x m) :=
    Finset.sum_nonneg (fun m _ => blockProgress_nonneg _)
  have hs1 : (∑ m, blockProgress (coupledBlock x m)) ≤ (M : ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun (m : Fin M) _ => blockProgress_le_one hN (coupledBlock x m))
  refine ⟨mul_nonneg hc hs0, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hs1 hc
  dsimp [progressReward]
  simpa only [div_mul_eq_mul_div] using hm

theorem euclideanBlock_norm_le {M N : ℕ} (x : ChainSpace M N) (m : Fin M) :
    ‖euclideanBlock x m‖ ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le (blockNorms x) m
  rw [blockNorms_norm] at h
  change ‖‖euclideanBlock x m‖‖ ≤ ‖x‖ at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

theorem progressReward_lipschitz {M N : ℕ} (hN : 0 < N) :
    GloballyLipschitz ((4 / (N : ℝ)) * M * (3 * Real.sqrt N / 8))
      (progressReward (M := M) (N := N)) := by
  intro x y
  let C := 3 * Real.sqrt (N : ℝ) / 8
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hper (m : Fin M) :
      |blockProgress (coupledBlock x m) - blockProgress (coupledBlock y m)| ≤ C * ‖x - y‖ := by
    have h := euclideanProgress_abs_sub_le hN (euclideanBlock x m) (euclideanBlock y m)
    have heq : euclideanBlock x m - euclideanBlock y m = euclideanBlock (x - y) m := rfl
    rw [heq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (euclideanBlock_norm_le (x - y) m) hC)
  have hsum : |(∑ m, blockProgress (coupledBlock x m)) -
      ∑ m, blockProgress (coupledBlock y m)| ≤ (M : ℝ) * C * ‖x - y‖ := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ m, |blockProgress (coupledBlock x m) - blockProgress (coupledBlock y m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin M, C * ‖x - y‖ := Finset.sum_le_sum (fun m _ => hper m)
      _ = (M : ℝ) * C * ‖x - y‖ := by simp; ring
  dsimp [progressReward]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))]
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))
  dsimp [C] at hm
  nlinarith

theorem coupledFunction_global_lipschitz {M N : ℕ} (hN : 0 < N) :
    GloballyLipschitz (rawLipschitzConstant M N) (coupledFunction (M := M) (N := N)) := by
  intro x y
  rw [coupledFunction_eq_score_sub_reward, coupledFunction_eq_score_sub_reward]
  have heq : positiveScoreTerm x - progressReward x - (positiveScoreTerm y - progressReward y) =
      (positiveScoreTerm x - positiveScoreTerm y) - (progressReward x - progressReward y) := by ring
  rw [heq]
  have h := abs_sub (positiveScoreTerm x - positiveScoreTerm y) (progressReward x - progressReward y)
  have hs := positiveScoreTerm_lipschitz hN x y
  have hr := progressReward_lipschitz hN x y
  dsimp [rawLipschitzConstant]
  nlinarith

theorem rawLipschitzConstant_nonneg (M N : ℕ) : 0 ≤ rawLipschitzConstant M N := by
  dsimp [rawLipschitzConstant]
  positivity

def chainSourceRadius (M N : ℕ) : ℝ :=
  4 * (M : ℝ) / ((N : ℝ) * (2 - (1 / 4 + 3 / (2 * Real.sqrt N))))

theorem chain_source_radius {M N : ℕ} (hN : 256 ≤ N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) : ‖x - y‖ ≤ chainSourceRadius M N := by
  have hNpos : 0 < N := by omega
  let c : ℝ := 1 / 4 + 3 / (2 * Real.sqrt N)
  have hc : c ≤ 11 / 32 := positiveScoreTerm_lipschitzConstant_le hN
  have hden : 0 < 2 - c := by linarith
  have hs := (le_abs_self (positiveScoreTerm y - positiveScoreTerm x)).trans
    (positiveScoreTerm_lipschitz hNpos y x)
  rw [norm_sub_rev y x] at hs
  obtain ⟨hrx0, hrx1⟩ := progressReward_range hNpos x
  obtain ⟨hry0, hry1⟩ := progressReward_range hNpos y
  have hdiff : coupledFunction y - coupledFunction x ≤
      c * ‖x - y‖ + 4 * (M : ℝ) / N := by
    rw [coupledFunction_eq_score_sub_reward, coupledFunction_eq_score_sub_reward]
    change _ ≤ (1 / 4 + 3 / (2 * Real.sqrt N)) * ‖x - y‖ + _
    linarith
  have hr := source_radius_bound (chainMajorant_finite hNpos) hy hdiff
  have hbound : ‖x - y‖ ≤ (4 * (M : ℝ) / N) / (2 - c) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  convert hbound using 1
  dsimp [chainSourceRadius, c]
  field_simp

end WC
