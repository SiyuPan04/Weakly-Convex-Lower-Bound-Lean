import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Tilted max-affine blocks and the scalar progress gate

The coordinate indices in this file start at zero. `tiltIntercept K r` is
the manuscript's intercept at lexicographic rank `r + 1`.

The active-set locality theorem below concerns the actual finite maximum.
It does not claim the unformalized subdifferential representation theorem.
-/

namespace WC

noncomputable section

open scoped Classical
open scoped BigOperators

/-- The clipped cubic progress function from the manuscript. -/
def progressGate (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t < 1 then 3 * t ^ 2 - 2 * t ^ 3 else 1

theorem progressGate_of_nonpos {t : ℝ} (ht : t ≤ 0) : progressGate t = 0 := by
  simp [progressGate, ht]

theorem progressGate_of_one_le {t : ℝ} (ht : 1 ≤ t) : progressGate t = 1 := by
  have hp : 0 < t := by linarith
  simp [progressGate, not_le.mpr hp, not_lt.mpr ht]

theorem progressGate_of_mem_Ioo {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    progressGate t = 3 * t ^ 2 - 2 * t ^ 3 := by
  simp [progressGate, not_le.mpr h0, h1]

@[simp] theorem progressGate_zero : progressGate 0 = 0 := by
  exact progressGate_of_nonpos le_rfl

@[simp] theorem progressGate_one : progressGate 1 = 1 := by
  exact progressGate_of_one_le le_rfl

theorem progressGate_nonneg (t : ℝ) : 0 ≤ progressGate t := by
  by_cases h0 : t ≤ 0
  · simp [progressGate_of_nonpos h0]
  by_cases h1 : t < 1
  · rw [progressGate_of_mem_Ioo (lt_of_not_ge h0) h1]
    have : 0 ≤ t ^ 2 * (3 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  · simp [progressGate_of_one_le (le_of_not_gt h1)]

theorem progressGate_le_one (t : ℝ) : progressGate t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · simp [progressGate_of_nonpos h0]
  by_cases h1 : t < 1
  · rw [progressGate_of_mem_Ioo (lt_of_not_ge h0) h1]
    have : 0 ≤ (1 - t) ^ 2 * (1 + 2 * t) :=
      mul_nonneg (sq_nonneg (1 - t)) (by linarith)
    nlinarith
  · simp [progressGate_of_one_le (le_of_not_gt h1)]

/-- The polynomial derivative on the transition interval. -/
theorem hasDerivAt_progressGate_interior {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt progressGate (6 * t * (1 - t)) t := by
  have hp : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
      (6 * t * (1 - t)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul 3).sub
      (((hasDerivAt_id t).pow 3).const_mul 2) using 1 <;>
        first | rfl | (norm_num; ring)
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds h0 h1] with x hx
  exact progressGate_of_mem_Ioo hx.1 hx.2

/-- The derivative really vanishes on the flat lower branch. -/
theorem hasDerivAt_progressGate_of_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt progressGate 0 t := by
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with x hx
  exact progressGate_of_nonpos (le_of_lt hx)

/-- The derivative really vanishes on the flat upper branch. -/
theorem hasDerivAt_progressGate_of_one_lt {t : ℝ} (ht : 1 < t) :
    HasDerivAt progressGate 0 t := by
  apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact progressGate_of_one_le (le_of_lt hx)

private theorem gatePolynomial_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) (6 * t * (1 - t)) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul 3).sub
    (((hasDerivAt_id t).pow 3).const_mul 2) using 1 <;>
      first | rfl | (norm_num; ring)

private theorem gatePolynomial_on_unit {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    progressGate x = 3 * x ^ 2 - 2 * x ^ 3 := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst x
    norm_num
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst x
    norm_num
  exact progressGate_of_mem_Ioo h0 h1

/-- The two one-sided derivatives agree at the lower junction. -/
theorem hasDerivAt_progressGate_zero : HasDerivAt progressGate 0 0 := by
  have hl : HasDerivWithinAt progressGate 0 (Set.Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro x hx
      exact progressGate_of_nonpos hx
    · simp
  have hr : HasDerivWithinAt progressGate 0 (Set.Icc 0 1) 0 := by
    have hp : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) 0 0 := by
      simpa using gatePolynomial_hasDerivAt 0
    apply hp.hasDerivWithinAt.congr
    · intro x hx
      exact gatePolynomial_on_unit hx
    · norm_num
  apply (hl.union hr).hasDerivAt
  apply Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  by_cases h : x ≤ 0
  · exact Or.inl h
  · exact Or.inr ⟨le_of_not_ge h, le_of_lt hx⟩

/-- The two one-sided derivatives agree at the upper junction. -/
theorem hasDerivAt_progressGate_one : HasDerivAt progressGate 0 1 := by
  have hl : HasDerivWithinAt progressGate 0 (Set.Icc 0 1) 1 := by
    have hp : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) 0 1 := by
      simpa using gatePolynomial_hasDerivAt 1
    apply hp.hasDerivWithinAt.congr
    · intro x hx
      exact gatePolynomial_on_unit hx
    · norm_num
  have hr : HasDerivWithinAt progressGate 0 (Set.Ici 1) 1 := by
    apply (hasDerivAt_const (1 : ℝ) (1 : ℝ)).hasDerivWithinAt.congr
    · intro x hx
      exact progressGate_of_one_le hx
    · simp
  apply (hl.union hr).hasDerivAt
  apply Filter.mem_of_superset (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  by_cases h : x ≤ 1
  · exact Or.inl ⟨le_of_lt hx, h⟩
  · exact Or.inr (le_of_not_ge h)

theorem differentiable_progressGate : Differentiable ℝ progressGate := by
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · exact (hasDerivAt_progressGate_of_neg ht).differentiableAt
  · subst t
    exact hasDerivAt_progressGate_zero.differentiableAt
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · exact (hasDerivAt_progressGate_interior ht h1).differentiableAt
  · subst t
    exact hasDerivAt_progressGate_one.differentiableAt
  · exact (hasDerivAt_progressGate_of_one_lt h1).differentiableAt

theorem continuous_progressGate : Continuous progressGate :=
  differentiable_progressGate.continuous

theorem interior_progressGate_slope_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ 6 * t * (1 - t) := by positivity

theorem interior_progressGate_slope_le {t : ℝ} : 6 * t * (1 - t) ≤ 3 / 2 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

def progressGateSlope (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t < 1 then 6 * t * (1 - t) else 0

theorem hasDerivAt_progressGate (t : ℝ) : HasDerivAt progressGate (progressGateSlope t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · simpa [progressGateSlope, le_of_lt ht] using hasDerivAt_progressGate_of_neg ht
  · subst t
    simpa [progressGateSlope] using hasDerivAt_progressGate_zero
  rcases lt_trichotomy t 1 with h1 | h1 | h1
  · simpa [progressGateSlope, not_le.mpr ht, h1] using hasDerivAt_progressGate_interior ht h1
  · subst t
    simpa [progressGateSlope] using hasDerivAt_progressGate_one
  · simpa [progressGateSlope, not_le.mpr ht, not_lt.mpr (le_of_lt h1)] using
      hasDerivAt_progressGate_of_one_lt h1

@[simp] theorem deriv_progressGate (t : ℝ) : deriv progressGate t = progressGateSlope t :=
  (hasDerivAt_progressGate t).deriv

theorem progressGateSlope_nonneg (t : ℝ) : 0 ≤ progressGateSlope t := by
  unfold progressGateSlope
  split_ifs with h0 h1
  · rfl
  · exact interior_progressGate_slope_nonneg (le_of_not_ge h0) (le_of_lt h1)
  · rfl

theorem progressGateSlope_le (t : ℝ) : progressGateSlope t ≤ 3 / 2 := by
  unfold progressGateSlope
  split_ifs with h0 h1
  · norm_num
  · exact interior_progressGate_slope_le
  · norm_num

theorem monotone_progressGate : Monotone progressGate :=
  monotone_of_deriv_nonneg differentiable_progressGate fun x => by
    rw [deriv_progressGate]
    exact progressGateSlope_nonneg x

private theorem progressGateSlope_abs_sub_le_of_le {x y : ℝ} (hxy : x ≤ y) :
    |progressGateSlope y - progressGateSlope x| ≤ 6 * (y - x) := by
  by_cases hx0 : x ≤ 0
  · by_cases hy0 : y ≤ 0
    · simp only [progressGateSlope, if_pos hx0, if_pos hy0, sub_self, abs_zero]
      linarith
    by_cases hy1 : y < 1
    · simp only [progressGateSlope, if_pos hx0, if_neg hy0, if_pos hy1, sub_zero]
      rw [abs_of_nonneg (interior_progressGate_slope_nonneg (le_of_not_ge hy0) (le_of_lt hy1))]
      nlinarith [sq_nonneg y]
    · simp only [progressGateSlope, if_pos hx0, if_neg hy0, if_neg hy1, sub_self, abs_zero]
      linarith
  by_cases hx1 : x < 1
  · have hxpos : 0 ≤ x := le_of_not_ge hx0
    have hy0 : ¬ y ≤ 0 := by linarith
    by_cases hy1 : y < 1
    · simp only [progressGateSlope, if_neg hx0, if_pos hx1, if_neg hy0, if_pos hy1]
      apply abs_le.mpr
      have hmul1 := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + y by linarith)
      have hmul2 := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2 - x - y by linarith)
      constructor <;> nlinarith
    · simp only [progressGateSlope, if_neg hx0, if_pos hx1, if_neg hy0, if_neg hy1, zero_sub,
        abs_neg]
      rw [abs_of_nonneg (interior_progressGate_slope_nonneg hxpos (le_of_lt hx1))]
      nlinarith [sq_nonneg (x - 1)]
  · have hy0 : ¬ y ≤ 0 := by linarith
    have hy1 : ¬ y < 1 := by linarith
    simp only [progressGateSlope, if_neg hx0, if_neg hx1, if_neg hy0, if_neg hy1,
      sub_self, abs_zero]
    linarith

/-- The global derivative bound used in the progress-function regularity proof. -/
theorem progressGateSlope_abs_sub_le (x y : ℝ) :
    |progressGateSlope x - progressGateSlope y| ≤ 6 * |x - y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm (progressGateSlope x), abs_sub_comm x, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact progressGateSlope_abs_sub_le_of_le hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact progressGateSlope_abs_sub_le_of_le hyx

theorem lipschitzWith_progressGateSlope : LipschitzWith 6 progressGateSlope := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using progressGateSlope_abs_sub_le x y

/-- The relay gate is zero until a quarter of the progress is reached. -/
theorem relayGate_zero {s : ℝ} (hs : s ≤ 1 / 4) :
    progressGate ((4 * s - 1) / 3) = 0 := by
  apply progressGate_of_nonpos
  linarith

/-- The shift used in the manuscript makes zero coordinates strictly flat. -/
theorem shifted_zero_flat {N : ℕ} (hN : 0 < N) :
    progressGate (-(1 / (64 * (N : ℝ)))) = 0 ∧
    HasDerivAt progressGate 0 (-(1 / (64 * (N : ℝ)))) := by
  have hp : 0 < 1 / (64 * (N : ℝ)) := by positivity
  exact ⟨progressGate_of_nonpos (by linarith),
    hasDerivAt_progressGate_of_neg (by linarith)⟩

/-- The average progress of one block. -/
def blockProgress {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  (∑ n, progressGate ((N : ℝ) / 4 * u n - 1 / (64 * (N : ℝ)))) / N

theorem blockProgress_nonneg {N : ℕ} (u : Fin N → ℝ) : 0 ≤ blockProgress u := by
  unfold blockProgress
  exact div_nonneg (Finset.sum_nonneg fun _ _ => progressGate_nonneg _) (by positivity)

theorem blockProgress_le_one {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ) :
    blockProgress u ≤ 1 := by
  unfold blockProgress
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ _ : Fin N, (1 : ℝ) := Finset.sum_le_sum fun _ _ => progressGate_le_one _
    _ = 1 * (N : ℝ) := by simp

/-- Zero coordinates contribute zero to progress. -/
theorem zero_coordinate_progress {N : ℕ} {u : Fin N → ℝ} {n : Fin N} (hn : u n = 0) :
    progressGate ((N : ℝ) / 4 * u n - 1 / (64 * (N : ℝ))) = 0 := by
  apply progressGate_of_nonpos
  rw [hn]
  simp only [mul_zero, zero_sub]
  exact neg_nonpos.mpr (by positivity)

@[simp] theorem blockProgress_zero (N : ℕ) : blockProgress (fun _ : Fin N => 0) = 0 := by
  unfold blockProgress
  have h : progressGate ((N : ℝ) / 4 * 0 - 1 / (64 * (N : ℝ))) = 0 := by
    apply progressGate_of_nonpos
    simp only [mul_zero, zero_sub]
    exact neg_nonpos.mpr (by positivity)
  simp only [h, Finset.sum_const_zero, zero_div]

/-- Progress is bounded by the fraction of nonzero coordinates, as used by the relay. -/
theorem blockProgress_le_support_fraction {N : ℕ} (u : Fin N → ℝ) :
    blockProgress u ≤ ((Finset.univ.filter fun n => u n ≠ 0).card : ℝ) / N := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ n : Fin N, if u n ≠ 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      by_cases h : u n = 0
      · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
        simpa only [h] using le_of_eq (zero_coordinate_progress h)
      · simpa only [h, ne_eq, not_false_eq_true, ↓reduceIte] using progressGate_le_one
          ((N : ℝ) / 4 * u n - 1 / (64 * (N : ℝ)))
    _ = ((Finset.univ.filter fun n => u n ≠ 0).card : ℝ) :=
      Finset.sum_boole (fun n => u n ≠ 0) Finset.univ

/-- Crossing the relay threshold requires progress on more than a quarter of the coordinates. -/
theorem relay_requires_support {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ)
    (hp : 1 / 4 < blockProgress u) :
    (N : ℝ) / 4 < (Finset.univ.filter fun n => u n ≠ 0).card := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := lt_of_lt_of_le hp (blockProgress_le_support_fraction u)
  have hmul := (lt_div_iff₀ hpos).mp h
  linarith

/-- The intercept at zero-based lexicographic rank `r`. -/
def tiltIntercept (K r : ℕ) : ℝ :=
  1 + ((K : ℝ) - (r : ℝ)) / (32 * ((K : ℝ) + 1))

theorem tiltIntercept_gt_one {K r : ℕ} (hr : r < K) :
    1 < tiltIntercept K r := by
  have hcast : (r : ℝ) < K := by exact_mod_cast hr
  have : 0 < ((K : ℝ) - (r : ℝ)) / (32 * ((K : ℝ) + 1)) := by positivity
  unfold tiltIntercept
  linarith

theorem tiltIntercept_lt {K r : ℕ} : tiltIntercept K r < 33 / 32 := by
  unfold tiltIntercept
  have hd : 0 < 32 * ((K : ℝ) + 1) := by positivity
  have hr : 0 ≤ (r : ℝ) := by positivity
  have h : ((K : ℝ) - (r : ℝ)) / (32 * ((K : ℝ) + 1)) < 1 / 32 := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  linarith

theorem tiltIntercept_strictAnti {K r s : ℕ} (hrs : r < s) :
    tiltIntercept K s < tiltIntercept K r := by
  unfold tiltIntercept
  have hcast : (r : ℝ) < s := by exact_mod_cast hrs
  have hd : 0 < 32 * ((K : ℝ) + 1) := by positivity
  have hh : ((K : ℝ) - (s : ℝ)) / (32 * ((K : ℝ) + 1)) <
      ((K : ℝ) - (r : ℝ)) / (32 * ((K : ℝ) + 1)) :=
    (div_lt_div_iff_of_pos_right hd).mpr (by linarith)
  linarith

def fanPiece (N K m : ℕ) (u : Fin N → ℝ) (n : Fin N) : ℝ :=
  tiltIntercept K (m * N + n.val) - (N : ℝ) / 8 * u n

/-- The genuine finite maximum, including the constant zero piece. -/
def tiltedBlock (N K m : ℕ) (u : Fin N → ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (fanPiece N K m u))).sup'
    (Finset.insert_nonempty _ _) id

theorem fanPiece_le_tiltedBlock (N K m : ℕ) (u : Fin N → ℝ) (n : Fin N) :
    fanPiece N K m u n ≤ tiltedBlock N K m u := by
  unfold tiltedBlock
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩

theorem tiltedBlock_nonneg (N K m : ℕ) (u : Fin N → ℝ) :
    0 ≤ tiltedBlock N K m u := by
  unfold tiltedBlock
  exact Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem tiltedBlock_le {N K m : ℕ} {u : Fin N → ℝ} {a : ℝ}
    (h0 : 0 ≤ a) (hp : ∀ n, fanPiece N K m u n ≤ a) : tiltedBlock N K m u ≤ a := by
  unfold tiltedBlock
  apply Finset.sup'_le
  intro b hb
  rcases Finset.mem_insert.mp hb with hb | hb
  · simpa only [hb, id_eq] using h0
  · rcases Finset.mem_image.mp hb with ⟨n, _, rfl⟩
    exact hp n

theorem convexOn_tiltedBlock (N K m : ℕ) :
    ConvexOn ℝ Set.univ (tiltedBlock N K m) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change tiltedBlock N K m (a • x + b • y) ≤
    a * tiltedBlock N K m x + b * tiltedBlock N K m y
  apply tiltedBlock_le
  · exact add_nonneg (mul_nonneg ha (tiltedBlock_nonneg N K m x))
      (mul_nonneg hb (tiltedBlock_nonneg N K m y))
  · intro n
    have heq : fanPiece N K m (a • x + b • y) n =
        a * fanPiece N K m x n + b * fanPiece N K m y n := by
      have hc : (a + b) * tiltIntercept K (m * N + n.val) =
          tiltIntercept K (m * N + n.val) := by rw [hab]; ring
      simp only [fanPiece, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hc]
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_left (fanPiece_le_tiltedBlock N K m x n) ha)
      (mul_le_mul_of_nonneg_left (fanPiece_le_tiltedBlock N K m y n) hb)

/-- Among zero tail coordinates, the first one strictly dominates every later one. -/
theorem fanPiece_lt_first_unrevealed {N K m : ℕ} (u : Fin N → ℝ)
    (k n : Fin N) (hkn : k < n) (hk : u k = 0) (hn : u n = 0) :
    fanPiece N K m u n < fanPiece N K m u k := by
  simp only [fanPiece, hk, hn, mul_zero, sub_zero]
  apply tiltIntercept_strictAnti
  exact Nat.add_lt_add_left hkn _

/-- No affine piece strictly beyond the first unrevealed coordinate is active. -/
theorem active_fanPiece_locality {N K m : ℕ} (u : Fin N → ℝ) (k : Fin N)
    (htail : ∀ n : Fin N, k ≤ n → u n = 0) (n : Fin N)
    (hactive : fanPiece N K m u n = tiltedBlock N K m u) : n ≤ k := by
  by_contra h
  have hkn : k < n := lt_of_not_ge h
  have hlt := fanPiece_lt_first_unrevealed (K := K) (m := m) u k n hkn
    (htail k le_rfl) (htail n (le_of_lt hkn))
  have hle := fanPiece_le_tiltedBlock N K m u k
  linarith

/-- The usual convex subgradient inequality, written in finite coordinates. -/
def IsTiltedBlockSubgradient {N : ℕ} (K m : ℕ) (u g : Fin N → ℝ) : Prop :=
  ∀ y, tiltedBlock N K m u + ∑ i, g i * (y i - u i) ≤ tiltedBlock N K m y

def coordinatePerturb {N : ℕ} (u : Fin N → ℝ) (n : Fin N) (d : ℝ) : Fin N → ℝ :=
  Function.update u n (u n + d)

theorem sum_coordinatePerturb {N : ℕ} (u g : Fin N → ℝ) (n : Fin N) (d : ℝ) :
    (∑ i, g i * (coordinatePerturb u n d i - u i)) = g n * d := by
  rw [Finset.sum_eq_single n]
  · simp [coordinatePerturb]
  · intro i _ hin
    simp [coordinatePerturb, Function.update_of_ne hin]
  · simp

theorem fanPiece_coordinatePerturb_self {N K m : ℕ} (u : Fin N → ℝ)
    (n : Fin N) (d : ℝ) :
    fanPiece N K m (coordinatePerturb u n d) n =
      fanPiece N K m u n - (N : ℝ) / 8 * d := by
  simp only [fanPiece, coordinatePerturb, Function.update_self]
  ring

theorem fanPiece_coordinatePerturb_ne {N K m : ℕ} (u : Fin N → ℝ)
    (n i : Fin N) (d : ℝ) (hin : i ≠ n) :
    fanPiece N K m (coordinatePerturb u n d) i = fanPiece N K m u i := by
  simp [fanPiece, coordinatePerturb, Function.update_of_ne hin]

theorem tiltedBlock_coordinatePerturb_le {N K m : ℕ} (u : Fin N → ℝ)
    (n : Fin N) (d : ℝ)
    (hn : fanPiece N K m u n - (N : ℝ) / 8 * d ≤ tiltedBlock N K m u) :
    tiltedBlock N K m (coordinatePerturb u n d) ≤ tiltedBlock N K m u := by
  apply tiltedBlock_le (tiltedBlock_nonneg N K m u)
  intro i
  by_cases hin : i = n
  · subst i
    rw [fanPiece_coordinatePerturb_self]
    exact hn
  · rw [fanPiece_coordinatePerturb_ne u n i d hin]
    exact fanPiece_le_tiltedBlock N K m u i

/-- Every convex subgradient is zero beyond the first unrevealed coordinate.

This proves the support conclusion directly from the subgradient inequality,
without postulating an active-slope representation.
-/
theorem tiltedBlock_subgradient_locality {N K m : ℕ} (u g : Fin N → ℝ) (k : Fin N)
    (htail : ∀ n : Fin N, k ≤ n → u n = 0)
    (hg : IsTiltedBlockSubgradient K m u g) (n : Fin N) (hkn : k < n) : g n = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have ha : 0 < (N : ℝ) / 8 := by positivity
  have hlt := fanPiece_lt_first_unrevealed (K := K) (m := m) u k n hkn
    (htail k le_rfl) (htail n (le_of_lt hkn))
  have hk := fanPiece_le_tiltedBlock N K m u k
  have hn := fanPiece_le_tiltedBlock N K m u n
  let d : ℝ := (fanPiece N K m u k - fanPiece N K m u n) / ((N : ℝ) / 8)
  have hd : 0 < d := div_pos (sub_pos.mpr hlt) ha
  have hdid : (N : ℝ) / 8 * d = fanPiece N K m u k - fanPiece N K m u n := by
    dsimp [d]
    field_simp [ne_of_gt hN]
  have hpos := hg (coordinatePerturb u n 1)
  rw [sum_coordinatePerturb] at hpos
  have hmaxpos := tiltedBlock_coordinatePerturb_le (K := K) (m := m) u n 1 (by nlinarith)
  have hnonpos : g n ≤ 0 := by linarith
  have hneg := hg (coordinatePerturb u n (-d))
  rw [sum_coordinatePerturb] at hneg
  have hmaxneg := tiltedBlock_coordinatePerturb_le (K := K) (m := m) u n (-d) (by nlinarith)
  have hnonneg : 0 ≤ g n := by
    by_contra h
    have hgn : g n < 0 := lt_of_not_ge h
    have hp : 0 < g n * (-d) := mul_pos_of_neg_of_neg hgn (by linarith)
    linarith
  exact le_antisymm hnonpos hnonneg

end

end WC
