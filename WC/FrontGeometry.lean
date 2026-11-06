import WC.RemoteFanEquation
import WC.LocalityPerturbation

/-! Exact two-coordinate perturbation identities used to exclude a future source block. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

def pairDirection (i j : ι) (u v : ℝ) : EuclideanSpace ℝ ι :=
  EuclideanSpace.single i u + EuclideanSpace.single j v

def pairShift (x : EuclideanSpace ℝ ι) (i j : ι) (u v t : ℝ) : EuclideanSpace ℝ ι :=
  x + t • pairDirection i j u v

omit [Fintype ι] in
theorem pairShift_left (x : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j) (u v t : ℝ) :
    pairShift x i j u v t i = x i + t * u := by
  simp [pairShift, pairDirection, Ne.symm hij]

omit [Fintype ι] in
theorem pairShift_right (x : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j) (u v t : ℝ) :
    pairShift x i j u v t j = x j + t * v := by
  simp [pairShift, pairDirection, hij]

omit [Fintype ι] in
theorem pairShift_other (x : EuclideanSpace ℝ ι) (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j) (u v t : ℝ) :
    pairShift x i j u v t k = x k := by simp [pairShift, pairDirection, hki, hkj]

theorem inner_pairDirection (x : EuclideanSpace ℝ ι) (i j : ι) (u v : ℝ) :
    inner ℝ x (pairDirection i j u v) = u * x i + v * x j := by
  simp [pairDirection, inner_add_right, EuclideanSpace.inner_single_right]

theorem pairDirection_norm_sq {i j : ι} (hij : i ≠ j) (u v : ℝ) :
    ‖pairDirection i j u v‖ ^ 2 = u ^ 2 + v ^ 2 := by
  simp [pairDirection, norm_add_sq_real, EuclideanSpace.inner_single_left, hij]

theorem pairShift_norm_sq (x : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j) (u v t : ℝ) :
    ‖pairShift x i j u v t‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (u * x i + v * x j) + t ^ 2 * (u ^ 2 + v ^ 2) := by
  unfold pairShift
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_pairDirection, pairDirection_norm_sq hij]
  ring

theorem pairShift_distance_sq (x y : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j) (u v t : ℝ) :
    ‖x - pairShift y i j u v t‖ ^ 2 = ‖x - y‖ ^ 2 -
      2 * t * (u * (x i - y i) + v * (x j - y j)) + t ^ 2 * (u ^ 2 + v ^ 2) := by
  have heq : x - pairShift y i j u v t = pairShift (x - y) i j u v (-t) := by
    unfold pairShift
    module
  rw [heq, pairShift_norm_sq _ hij]
  simp only [PiLp.sub_apply]
  ring

theorem front_source_distance_sq (x y : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j)
    {R α β : ℝ} (hR : ‖x - y‖ = R) (hi : x i - y i = R * α / 8)
    (hj : x j - y j = R * β / 8) (t : ℝ) :
    ‖x - pairShift y i j (-β) α t‖ ^ 2 = R ^ 2 + (α ^ 2 + β ^ 2) * t ^ 2 := by
  rw [pairShift_distance_sq _ _ hij, hR, hi, hj]
  ring

theorem front_score_norm_sq (p : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j)
    {S α β a : ℝ} (hS : ‖p‖ = S) (hi : p i = S * α) (hj : p j = S * β) (t : ℝ) :
    ‖pairShift p i j (a * β) (-(a * α)) t‖ ^ 2 = S ^ 2 + a ^ 2 * (α ^ 2 + β ^ 2) * t ^ 2 := by
  rw [pairShift_norm_sq _ hij, hS, hi, hj]
  ring

/-- Moving two nonnegative positive-score entries into one strictly larger entry raises the full norm. -/
theorem positive_pair_trade_norm_strict (p q : EuclideanSpace ℝ ι) {i j : ι} (hij : i ≠ j)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) (hjzero : q j = 0)
    (hgain : p i + p j < q i) (hsame : ∀ k, k ≠ i → k ≠ j → q k = p k) : ‖p‖ < ‖q‖ := by
  have hsum : (∑ k, q k ^ 2) - (∑ k, p k ^ 2) = q i ^ 2 - p i ^ 2 - p j ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    have heq : (∑ k, (q k ^ 2 - p k ^ 2)) =
        (q i ^ 2 - p i ^ 2) + (q j ^ 2 - p j ^ 2) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add _ _ (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])]
      have hz : (∑ k ∈ (Finset.univ.erase i).erase j, (q k ^ 2 - p k ^ 2)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        rw [hsame k hki hkj, sub_self]
      rw [hz]
      ring
    rw [heq, hjzero]
    ring
  have hstrict : ‖p‖ ^ 2 < ‖q‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have hi := hp i
    have hj := hp j
    have hqi := hq i
    nlinarith [mul_nonneg hi hj]
  nlinarith [norm_nonneg p, norm_nonneg q]

theorem positiveScores_eq_norm_smul_optimizer (s : EuclideanSpace ℝ ι) :
    positiveScores s = ‖positiveScores s‖ • positiveScoreOptimizer s := by
  by_cases hp : positiveScores s = 0
  · simp [hp]
  · have hnorm : ‖positiveScores s‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    unfold positiveScoreOptimizer
    rw [if_neg hp, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

end WC
