import WC.RawLipschitz

/-! Coordinate exchange identities for the separable progress reward. -/

noncomputable section
namespace WC
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def coordinateInf (x y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => min (x i) (y i))

def coordinateSup (x y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => max (x i) (y i))

theorem lattice_norm_sq_add (x y : EuclideanSpace ℝ ι) :
    ‖coordinateInf x y‖ ^ 2 + ‖coordinateSup x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, coordinateInf, coordinateSup]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≤ y i
  · simp only [min_eq_left hi, max_eq_right hi]
  · simp only [min_eq_right (le_of_not_ge hi), max_eq_left (le_of_not_ge hi)]
    ring

theorem lattice_inf_sq_le_inner {x y : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ‖coordinateInf x y‖ ^ 2 ≤ inner ℝ x y := by
  simp only [EuclideanSpace.real_norm_sq_eq, coordinateInf, PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ≤ y i
  · simp only [min_eq_left hi]
    nlinarith [mul_nonneg (hx i) (sub_nonneg.mpr hi)]
  · simp only [min_eq_right (le_of_not_ge hi)]
    nlinarith [mul_nonneg (hy i) (sub_nonneg.mpr (le_of_not_ge hi))]

theorem lattice_inf_norm_le_sup {x y : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ‖coordinateInf x y‖ ≤ ‖coordinateSup x y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, coordinateInf, coordinateSup]
  apply Finset.sum_le_sum
  intro i _
  have hmin : 0 ≤ min (x i) (y i) := le_min (hx i) (hy i)
  have hmax : min (x i) (y i) ≤ max (x i) (y i) := min_le_max
  exact (sq_le_sq₀ hmin (le_trans hmin hmax)).mpr hmax

theorem upper_sub_coordinateInf (z x y : EuclideanSpace ℝ ι) :
    z - coordinateInf x y = coordinateSup (z - x) (z - y) := by
  ext i
  change z i - min (x i) (y i) = max (z i - x i) (z i - y i)
  by_cases hi : x i ≤ y i
  · rw [min_eq_left hi, max_eq_left (by linarith)]
  · rw [min_eq_right (le_of_not_ge hi), max_eq_right (by linarith)]

theorem upper_sub_coordinateSup (z x y : EuclideanSpace ℝ ι) :
    z - coordinateSup x y = coordinateInf (z - x) (z - y) := by
  ext i
  change z i - max (x i) (y i) = min (z i - x i) (z i - y i)
  by_cases hi : x i ≤ y i
  · rw [max_eq_right hi, min_eq_right (by linarith)]
  · rw [max_eq_left (le_of_not_ge hi), min_eq_left (by linarith)]

theorem coordinateSup_sub_left (x y : EuclideanSpace ℝ ι) :
    coordinateSup x y - x = y - coordinateInf x y := by
  ext i
  change max (x i) (y i) - x i = y i - min (x i) (y i)
  by_cases hi : x i ≤ y i
  · simp only [max_eq_right hi, min_eq_left hi]
  · simp only [max_eq_left (le_of_not_ge hi), min_eq_right (le_of_not_ge hi), sub_self]

theorem coordinateSup_distance_le {z x y : EuclideanSpace ℝ ι}
    (hx : ∀ i, x i ≤ z i) (hy : ∀ i, y i ≤ z i) :
    ‖coordinateSup x y - x‖ ≤ ‖z - x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, coordinateSup, PiLp.sub_apply]
  apply Finset.sum_le_sum
  intro i _
  have hdiff0 : 0 ≤ max (x i) (y i) - x i := sub_nonneg.mpr (le_max_left _ _)
  have hdiff : max (x i) (y i) - x i ≤ z i - x i :=
    sub_le_sub_right (max_le (hx i) (hy i)) _
  exact (sq_le_sq₀ hdiff0 (sub_nonneg.mpr (hx i))).mpr hdiff

theorem progressReward_lattice_exchange {M N : ℕ} (x y : ChainSpace M N) :
    progressReward x + progressReward y =
      progressReward (coordinateInf x y) + progressReward (coordinateSup x y) := by
  have hblock (m : Fin M) :
      blockProgress (coupledBlock x m) + blockProgress (coupledBlock y m) =
        blockProgress (coupledBlock (coordinateInf x y) m) +
          blockProgress (coupledBlock (coordinateSup x y) m) := by
    unfold blockProgress
    rw [← add_div, ← add_div]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hi : x (m, n) ≤ y (m, n)
    · simp only [coupledBlock, coordinateInf, coordinateSup, min_eq_left hi, max_eq_right hi]
    · simp only [coupledBlock, coordinateInf, coordinateSup,
        min_eq_right (le_of_not_ge hi), max_eq_left (le_of_not_ge hi)]
      ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun m _ => hblock m)
  simp only [Finset.sum_add_distrib] at hs
  have hm := congrArg (fun r : ℝ => 4 / (N : ℝ) * r) hs
  dsimp [progressReward]
  nlinarith

end WC
