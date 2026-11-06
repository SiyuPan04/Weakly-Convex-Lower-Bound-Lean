import WC.MajorantSources
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Coordinatewise monotonicity forces every attained source below its query. -/

noncomputable section
namespace WC

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def capAt (x y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => min (y i) (x i))

theorem capAt_distance_strict {x y : EuclideanSpace ℝ ι} (j : ι) (hj : x j < y j) :
    ‖x - capAt x y‖ < ‖x - y‖ := by
  have hs : ‖x - capAt x y‖ ^ 2 < ‖x - y‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, capAt, PiLp.sub_apply, PiLp.toLp_apply]
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : y i ≤ x i
      · rw [min_eq_left hi]
      · rw [min_eq_right (le_of_not_ge hi), sub_self, zero_pow (by norm_num)]
        exact sq_nonneg _
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      rw [min_eq_right hj.le, sub_self, zero_pow (by norm_num)]
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hj.ne)
  nlinarith [norm_nonneg (x - capAt x y), norm_nonneg (x - y)]

theorem majorant_source_coord_le {f : EuclideanSpace ℝ ι → ℝ} {L : ℝ}
    (hL : 0 < L) (hfinite : MajorantFinite f L)
    (hanti : ∀ u v, (∀ i, u i ≤ v i) → f v ≤ f u)
    {x y : EuclideanSpace ℝ ι} (hy : y ∈ majorantSources f L x) :
    ∀ i, y i ≤ x i := by
  intro i
  by_contra hi
  have hlt : x i < y i := lt_of_not_ge hi
  have hcap := hanti (capAt x y) y (fun j => min_le_left _ _)
  have hdist := mul_lt_mul_of_pos_left (capAt_distance_strict i hlt) hL
  have hpay := payoff_le_majorant hfinite x (capAt x y)
  change sourcePayoff f L x y = lipschitzMajorant f L x at hy
  dsimp [sourcePayoff] at hy hpay
  linarith

end WC
