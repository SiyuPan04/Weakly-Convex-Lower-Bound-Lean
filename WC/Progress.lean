import WC.Block
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual derivatives and quantitative estimates for the block progress function. -/

noncomputable section

namespace WC

open scoped BigOperators

def euclideanProgress {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  blockProgress (fun n => x n)

def progressGradient {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun n => progressGateSlope ((N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ))) / 4)

theorem hasGradientAt_euclideanProgress {N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin N)) : HasGradientAt euclideanProgress (progressGradient x) x := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  let pr (n : Fin N) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) n
  have harg (n : Fin N) : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin N) => (N : ℝ) / 4 * y n - 1 / (64 * (N : ℝ)))
      (((N : ℝ) / 4) • pr n) x := by
    exact ((pr n).hasFDerivAt.const_mul ((N : ℝ) / 4)).sub_const _
  have hterm (n : Fin N) :=
    (hasDerivAt_progressGate ((N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ)))).comp_hasFDerivAt x (harg n)
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) (fun n _ => hterm n)).const_mul (1 / (N : ℝ))
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf : euclideanProgress (N := N) =
      (fun y => 1 / (N : ℝ) * ∑ n, progressGate ((N : ℝ) / 4 * y n - 1 / (64 * (N : ℝ)))) := by
    funext y
    dsimp [euclideanProgress, blockProgress]
    ring
  have hd : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))) (progressGradient x) =
      ((1 / (N : ℝ)) • ∑ n, progressGateSlope ((N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ))) •
        ((N : ℝ) / 4) • pr n) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, progressGradient, PiLp.inner_apply,
      smul_eq_mul, pr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    field_simp
  rw [hf, hd]
  exact hsum

theorem progressGradient_nonneg {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (n : Fin N) :
    0 ≤ progressGradient x n := by
  exact div_nonneg (progressGateSlope_nonneg _) (by norm_num)

theorem progressGradient_coordinate_le {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (n : Fin N) :
    progressGradient x n ≤ 3 / 8 := by
  change progressGateSlope _ / 4 ≤ 3 / 8
  have h := progressGateSlope_le ((N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ)))
  linarith

theorem progressGradient_norm_le {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    ‖progressGradient x‖ ≤ 3 * Real.sqrt (N : ℝ) / 8 := by
  have hs : ‖progressGradient x‖ ^ 2 ≤ (N : ℝ) * (3 / 8 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin N, (3 / 8 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        exact (sq_le_sq₀ (progressGradient_nonneg x n) (by norm_num)).mpr
          (progressGradient_coordinate_le x n)
      _ = (N : ℝ) * (3 / 8 : ℝ) ^ 2 := by simp
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hn := norm_nonneg (progressGradient x)
  have hr := Real.sqrt_nonneg (N : ℝ)
  nlinarith

theorem progressGradient_coordinate_abs_sub_le {N : ℕ}
    (x y : EuclideanSpace ℝ (Fin N)) (n : Fin N) :
    |progressGradient x n - progressGradient y n| ≤
      (3 * (N : ℝ) / 8) * |x n - y n| := by
  let a := (N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ))
  let b := (N : ℝ) / 4 * y n - 1 / (64 * (N : ℝ))
  have harg : |a - b| = (N : ℝ) / 4 * |x n - y n| := by
    have heq : a - b = (N : ℝ) / 4 * (x n - y n) := by dsimp [a, b]; ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4)]
  change |progressGateSlope a / 4 - progressGateSlope b / 4| ≤ _
  calc
    _ = |progressGateSlope a - progressGateSlope b| / 4 := by
      rw [← sub_div, abs_div]
      norm_num
    _ ≤ (6 * |a - b|) / 4 :=
      div_le_div_of_nonneg_right (progressGateSlope_abs_sub_le a b) (by norm_num)
    _ = _ := by rw [harg]; ring

/-- The exact global Lipschitz estimate for the gradient of the progress function. -/
theorem progressGradient_norm_sub_le {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ‖progressGradient x - progressGradient y‖ ≤ (3 * (N : ℝ) / 8) * ‖x - y‖ := by
  have hc : 0 ≤ 3 * (N : ℝ) / 8 := by positivity
  have hs : ‖progressGradient x - progressGradient y‖ ^ 2 ≤
      (3 * (N : ℝ) / 8) ^ 2 * ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have h := (sq_le_sq₀ (abs_nonneg (progressGradient x n - progressGradient y n))
      (mul_nonneg hc (abs_nonneg (x n - y n)))).mpr
        (progressGradient_coordinate_abs_sub_le x y n)
    simpa only [PiLp.sub_apply, sq_abs, mul_pow] using h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

theorem euclideanProgress_abs_sub_le {N : ℕ} (hN : 0 < N)
    (x y : EuclideanSpace ℝ (Fin N)) :
    |euclideanProgress x - euclideanProgress y| ≤
      (3 * Real.sqrt (N : ℝ) / 8) * ‖x - y‖ := by
  have hdiff : ∀ z : EuclideanSpace ℝ (Fin N), DifferentiableAt ℝ euclideanProgress z :=
    fun z => (hasGradientAt_euclideanProgress hN z).differentiableAt
  have hbound : ∀ z : EuclideanSpace ℝ (Fin N),
      ‖fderiv ℝ euclideanProgress z‖ ≤ 3 * Real.sqrt (N : ℝ) / 8 := by
    intro z
    rw [(hasGradientAt_euclideanProgress hN z).hasFDerivAt.fderiv]
    simpa using progressGradient_norm_le z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => hdiff z) (fun z (_ : z ∈ Set.univ) => hbound z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem lipschitzWith_progressGate : LipschitzWith (3 / 2) progressGate := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_progressGate
  intro t
  rw [deriv_progressGate]
  change |progressGateSlope t| ≤ 3 / 2
  rw [abs_of_nonneg (progressGateSlope_nonneg t)]
  exact progressGateSlope_le t

theorem monotone_blockProgress {N : ℕ} : Monotone (blockProgress (N := N)) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro n _
  apply monotone_progressGate
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hxy n) (by positivity)) _

end WC
