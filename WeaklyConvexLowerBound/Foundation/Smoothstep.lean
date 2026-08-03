import Mathlib
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar smoothstep support

The weakly convex construction uses one clipped cubic smoothstep.  This file
contains its literal definition, its actual derivative at the splice points,
and the global Lipschitz estimate for that derivative.
-/

namespace WeaklyConvexLowerBound.Foundation

noncomputable section

/-- Clipped cubic smoothstep. -/
def sigma (s : ℝ) : ℝ :=
  if s ≤ 0 then 0
  else if s ≤ 1 then 3 * s ^ 2 - 2 * s ^ 3
  else 1

/-- Piecewise derivative of `sigma`. -/
def sigmaDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0
  else if s ≤ 1 then 6 * s - 6 * s ^ 2
  else 0

@[simp] theorem sigmaDeriv_zero : sigmaDeriv 0 = 0 := by
  norm_num [sigmaDeriv]

@[simp] theorem sigmaDeriv_one : sigmaDeriv 1 = 0 := by
  norm_num [sigmaDeriv]

theorem sigma_of_nonpos {s : ℝ} (h : s ≤ 0) : sigma s = 0 := by
  simp [sigma, h]

theorem sigma_of_one_le {s : ℝ} (h : 1 ≤ s) : sigma s = 1 := by
  rcases h.eq_or_lt with rfl | h
  · norm_num [sigma]
  · simp [sigma, not_le.mpr (by linarith : 0 < s), not_le.mpr h]

@[simp] theorem sigma_zero : sigma 0 = 0 := by norm_num [sigma]

@[simp] theorem sigma_one : sigma 1 = 1 := by norm_num [sigma]

private def sigmaPoly (x : ℝ) : ℝ := 3 * x ^ 2 - 2 * x ^ 3

private theorem hasDerivAt_sigmaPoly (x : ℝ) :
    HasDerivAt sigmaPoly (6 * x - 6 * x ^ 2) x := by
  unfold sigmaPoly
  have h2 := ((hasDerivAt_id x).pow 2).const_mul 3
  have h3 := ((hasDerivAt_id x).pow 3).const_mul 2
  have h := h2.sub h3
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at h
  change HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3) _ x at h
  exact h.congr_deriv (by ring)

private theorem sigma_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    sigma x = sigmaPoly x := by
  rcases hx.1.eq_or_lt with hzero | hpos
  · subst x
    norm_num [sigma, sigmaPoly]
  · simp [sigma, sigmaPoly, not_le.mpr hpos, hx.2]

private theorem hasDerivWithinAt_sigma_left_zero :
    HasDerivWithinAt sigma 0 (Set.Iic (0 : ℝ)) 0 := by
  refine (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact sigma_of_nonpos hx
  · exact sigma_zero

private theorem hasDerivWithinAt_sigma_middle (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt sigma (6 * x - 6 * x ^ 2) (Set.Icc (0 : ℝ) 1) x := by
  refine (hasDerivAt_sigmaPoly x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact sigma_eq_poly hy
  · exact sigma_eq_poly hx

private theorem hasDerivWithinAt_sigma_right_one :
    HasDerivWithinAt sigma 0 (Set.Ici (1 : ℝ)) 1 := by
  refine (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact sigma_of_one_le hx
  · exact sigma_one

private theorem hasDerivAt_sigma_zero : HasDerivAt sigma 0 0 := by
  have hm : HasDerivWithinAt sigma 0 (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using hasDerivWithinAt_sigma_middle 0 (by norm_num)
  have hu := hasDerivWithinAt_sigma_left_zero.union hm
  have hset : Set.Iic (0 : ℝ) ∪ Set.Icc 0 1 = Set.Iic 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 0
      · exact Or.inl hx
      · exact Or.inr ⟨le_of_not_ge hx, h⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))

private theorem hasDerivAt_sigma_one : HasDerivAt sigma 0 1 := by
  have hm : HasDerivWithinAt sigma 0 (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using hasDerivWithinAt_sigma_middle 1 (by norm_num)
  have hu := hm.union hasDerivWithinAt_sigma_right_one
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 1
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_not_ge hx)
  rw [hset] at hu
  exact hu.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- `sigmaDeriv` is the actual derivative of `sigma` everywhere. -/
theorem hasDerivAt_sigma (s : ℝ) : HasDerivAt sigma (sigmaDeriv s) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hc : HasDerivWithinAt sigma 0 (Set.Iic (0 : ℝ)) s := by
      refine (hasDerivAt_const (x := s) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        exact sigma_of_nonpos hx
      · exact sigma_of_nonpos hs.le
    have hd := hc.hasDerivAt (Iic_mem_nhds hs)
    simpa [sigmaDeriv, hs.le] using hd
  · simpa using hasDerivAt_sigma_zero
  · rcases lt_trichotomy s 1 with hs1 | rfl | hs1
    · have hm := hasDerivWithinAt_sigma_middle s ⟨hs.le, hs1.le⟩
      have hmem : Set.Icc (0 : ℝ) 1 ∈ nhds s := Icc_mem_nhds hs hs1
      have hd := hm.hasDerivAt hmem
      simpa [sigmaDeriv, not_le.mpr hs, hs1.le] using hd
    · simpa using hasDerivAt_sigma_one
    · have hc : HasDerivWithinAt sigma 0 (Set.Ici (1 : ℝ)) s := by
        refine (hasDerivAt_const (x := s) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
        · intro x hx
          exact sigma_of_one_le hx
        · exact sigma_of_one_le hs1.le
      have hd := hc.hasDerivAt (Ici_mem_nhds hs1)
      simpa [sigmaDeriv, not_le.mpr hs, not_le.mpr hs1] using hd

/-- The derivative of the smoothstep is globally `6`-Lipschitz. -/
theorem sigmaDeriv_abs_sub_le (x y : ℝ) :
    |sigmaDeriv x - sigmaDeriv y| ≤ 6 * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa [abs_sub_comm] using this y x hyx
  by_cases hy0 : y ≤ 0
  · have hx0 : x ≤ 0 := hxy.trans hy0
    simp [sigmaDeriv, hx0, hy0]
  by_cases hx0 : x ≤ 0
  · by_cases hy1 : y ≤ 1
    · have hypos : 0 < y := lt_of_not_ge hy0
      rw [sigmaDeriv, if_pos hx0, sigmaDeriv, if_neg (not_le.mpr hypos),
        if_pos hy1]
      have hp : 0 ≤ 6 * y - 6 * y ^ 2 := by
        nlinarith [mul_nonneg hypos.le (sub_nonneg.mpr hy1)]
      rw [zero_sub, abs_neg, abs_of_nonneg hp,
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      nlinarith [sq_nonneg y]
    · have hyone : 1 < y := lt_of_not_ge hy1
      rw [sigmaDeriv, if_pos hx0, sigmaDeriv,
        if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
        if_neg (not_le.mpr hyone)]
      simp
  · have hxpos : 0 < x := lt_of_not_ge hx0
    by_cases hx1 : x ≤ 1
    · by_cases hy1 : y ≤ 1
      · rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_pos hx1,
          sigmaDeriv, if_neg (not_le.mpr (hxpos.trans_le hxy)), if_pos hy1]
        have heq :
            (6 * x - 6 * x ^ 2) - (6 * y - 6 * y ^ 2) =
              6 * (x - y) * (1 - x - y) := by ring
        have hs : |1 - x - y| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        rw [heq, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
        nlinarith [abs_nonneg (x - y)]
      · have hyone : 1 < y := lt_of_not_ge hy1
        rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_pos hx1,
          sigmaDeriv, if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
          if_neg (not_le.mpr hyone)]
        have hp : 0 ≤ 6 * x - 6 * x ^ 2 := by
          nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hx1)]
        rw [sub_zero, abs_of_nonneg hp,
          abs_of_nonpos (sub_nonpos.mpr hxy)]
        nlinarith [sq_nonneg (1 - x)]
    · have hxone : 1 < x := lt_of_not_ge hx1
      have hyone : 1 < y := hxone.trans_le hxy
      rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_neg (not_le.mpr hxone),
        sigmaDeriv, if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
        if_neg (not_le.mpr hyone)]
      simp

end

end WeaklyConvexLowerBound.Foundation
