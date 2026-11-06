import WC.Oracle
import WC.CoupledRegularity
import WC.CoupledCurvature

/-! Coordinate monotonicity controls every actual subgradient, not a selection. -/

noncomputable section
namespace WC

variable {ι : Type*} [Fintype ι]

theorem WeakSubgradient.coordinate_nonpos {f : EuclideanSpace ℝ ι → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hanti : ∀ u v, (∀ i, u i ≤ v i) → f v ≤ f u)
    {x v : EuclideanSpace ℝ ι} (hv : WeakSubgradient ρ f x v) (i : ι) : v i ≤ 0 := by
  classical
  by_contra h
  have hi : 0 < v i := lt_of_not_ge h
  let t : ℝ := v i / (ρ + 1)
  have ht : 0 < t := div_pos hi (by linarith)
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have he : inner ℝ v e = v i := by
    dsimp [e]
    simpa using EuclideanSpace.inner_single_right i (1 : ℝ) v
  have hen : ‖e‖ = 1 := by simp [e]
  have hle : ∀ j, x j ≤ (x + t • e) j := by
    intro j
    change x j ≤ x j + t * e j
    have he0 : 0 ≤ e j := by simp [e, PiLp.single_apply]; split_ifs <;> norm_num
    nlinarith
  have hm := hanti x (x + t • e) hle
  have hs := hv (x + t • e)
  simp only [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, hen, mul_one, he] at hs
  have hrel : t * (ρ + 1) = v i := by dsimp [t]; field_simp
  have hrel₂ := congrArg (fun r : ℝ => r * t) hrel
  nlinarith [sq_pos_of_pos ht, mul_nonneg hρ (sq_nonneg t)]

theorem coupledFunction_subgradient_nonpos {M N : ℕ} (hN : 0 < N)
    {x v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x) : ∀ i, v i ≤ 0 := by
  have hs := (weakSubgradient_iff_frechet (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (weaklyConvex_coupledFunction hN)).mpr hv
  exact hs.coordinate_nonpos (by norm_num) coupledFunction_coordinate_antitone

end WC
