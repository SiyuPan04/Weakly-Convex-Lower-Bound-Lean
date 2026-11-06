import WC.SourceBandMixtures
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Nonnegative cross terms and the exact inverse-weight Cauchy bound for
aggregating the near source group with finitely many remote source bands. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem nonpositive_inner_nonneg {κ : Type*} [Fintype κ]
    {u v : EuclideanSpace ℝ κ} (hu : ∀ i, u i ≤ 0) (hv : ∀ i, v i ≤ 0) :
    0 ≤ inner ℝ u v := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg_of_nonpos_of_nonpos (hu i) (hv i))

theorem sum_norm_sq_le_norm_sum_sq {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (g : ι → E) (hpair : ∀ i j, 0 ≤ inner ℝ (g i) (g j)) :
    (∑ i, ‖g i‖ ^ 2) ≤ ‖∑ i, g i‖ ^ 2 := by
  have hrow (i : ι) : ‖g i‖ ^ 2 ≤ ∑ j, inner ℝ (g i) (g j) := by
    rw [← real_inner_self_eq_norm_sq]
    exact Finset.single_le_sum (fun j _ => hpair i j) (Finset.mem_univ i)
  have hnorm : ‖∑ i, g i‖ ^ 2 = ∑ i, ∑ j, inner ℝ (g i) (g j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    simp only [real_inner_comm]
  rw [hnorm]
  exact Finset.sum_le_sum (fun i _ => hrow i)

theorem inverse_group_bound {ι : Type*} [Fintype ι] (w A : ι → ℝ)
    (hA : ∀ i, 0 < A i) (hsum : ∑ i, w i = 1) :
    1 / (∑ i, A i) ≤ ∑ i, w i ^ 2 / A i := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ w (fun i _ => hA i)
  simpa only [hsum, one_pow] using h

theorem near_remote_group_aggregation {κ : Type*} [Fintype κ] {B : ℕ} {N : ℝ}
    (hN : 0 < N) (w : Fin (B + 1) → ℝ) (g : Fin (B + 1) → EuclideanSpace ℝ κ)
    (hsum : ∑ i, w i = 1) (hg : ∀ i j, g i j ≤ 0)
    (hnear : w 0 ^ 2 / (25 * N) ≤ ‖g 0‖ ^ 2)
    (hremote : ∀ i : Fin (B + 1), i ≠ 0 → w i ^ 2 / 8 ≤ ‖g i‖ ^ 2) :
    1 / (25 * N + 8 * (B : ℝ)) ≤ ‖∑ i, g i‖ ^ 2 := by
  let A : Fin (B + 1) → ℝ := fun i => if i = 0 then 25 * N else 8
  have hA : ∀ i, 0 < A i := by intro i; dsimp [A]; split_ifs <;> positivity
  have hAtotal : (∑ i, A i) = 25 * N + 8 * (B : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp [A]
    ring
  have hc := inverse_group_bound w A hA hsum
  rw [hAtotal] at hc
  have hlower : (∑ i, w i ^ 2 / A i) ≤ ∑ i, ‖g i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = 0
    · subst i
      simpa only [A, if_pos rfl] using hnear
    · simpa only [A, if_neg hi] using hremote i hi
  exact hc.trans (hlower.trans (sum_norm_sq_le_norm_sum_sq g
    (fun i j => nonpositive_inner_nonneg (hg i) (hg j))))

end WC

