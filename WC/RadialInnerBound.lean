import WC.ChainSources
import WC.SaturatedSubgradient
import WC.MonotoneSubgradient

/-! The radial inner-product bound for the entire actual majorant subdifferential. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem coordinate_cap_inner_lower {ι : Type*} [Fintype ι]
    {g y : EuclideanSpace ℝ ι} {c L : ℝ} (hc : 0 ≤ c)
    (hgnonpos : ∀ i, g i ≤ 0) (hcap : ∀ i, c < y i → g i = 0) (hnorm : ‖g‖ ≤ L) :
    -(c * L * Real.sqrt (Fintype.card ι : ℝ)) ≤ inner ℝ g y := by
  let one : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hone : ‖one‖ = Real.sqrt (Fintype.card ι : ℝ) := by
    have hs : ‖one‖ ^ 2 = (Fintype.card ι : ℝ) := by
      simp [one, EuclideanSpace.real_norm_sq_eq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card ι by positivity),
      Real.sqrt_nonneg (Fintype.card ι : ℝ), norm_nonneg one]
  have hi := real_inner_le_norm (-g) one
  have his : inner ℝ (-g) one = -(∑ i, g i) := by
    simp [one, PiLp.inner_apply, Real.inner_apply, Finset.sum_neg_distrib]
  rw [his, norm_neg, hone] at hi
  have hL := mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg (Fintype.card ι : ℝ))
  have hscaled := mul_le_mul_of_nonneg_left (hi.trans hL) hc
  have hpoint (i : ι) : c * g i ≤ g i * y i := by
    by_cases hy : y i ≤ c
    · have hm := mul_nonneg (neg_nonneg.mpr (hgnonpos i)) (sub_nonneg.mpr hy)
      nlinarith
    · rw [hcap i (lt_of_not_ge hy)]
      simp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  have hinner : inner ℝ g y = ∑ i, g i * y i := by simp [PiLp.inner_apply, Real.inner_apply, mul_comm]
  rw [hinner]
  nlinarith

def chainRadialConstant (M N : ℕ) : ℝ :=
  18 * Real.sqrt ((M * N : ℕ) : ℝ) / (N : ℝ) + 2 * chainSourceRadius M N

theorem chain_source_radial_inner_lower {M N : ℕ} (hN : 256 ≤ N)
    {z y g : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 z)
    (hg : g ∈ subdifferential coupledFunction y) :
    -chainRadialConstant M N ≤ inner ℝ g z := by
  have hNpos : 0 < N := by omega
  have hnorm := chain_source_subgradient_norm_le hNpos hy hg
  have hcap := coordinate_cap_inner_lower (by positivity : (0 : ℝ) ≤ 9 / (N : ℝ))
    (coupledFunction_subgradient_nonpos hNpos hg)
    (coupledFunction_subgradient_zero_of_large hNpos hg) hnorm
  have hrad := chain_source_radius hN hy
  have hdot := neg_le_of_abs_le (abs_real_inner_le_norm g (z - y))
  have hprod := mul_le_mul hnorm hrad (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  rw [inner_sub_right] at hdot
  have hcard : (Fintype.card (Fin M × Fin N) : ℝ) = ((M * N : ℕ) : ℝ) := by simp
  rw [hcard] at hcap
  dsimp [chainRadialConstant]
  have heq : (9 / (N : ℝ)) * 2 * Real.sqrt ((M * N : ℕ) : ℝ) =
      18 * Real.sqrt ((M * N : ℕ) : ℝ) / (N : ℝ) := by ring
  rw [heq] at hcap
  linarith

theorem chainMajorant_radial_inner_lower {M N : ℕ} (hN : 256 ≤ N)
    {z g : ChainSpace M N} (hg : g ∈ subdifferential chainMajorant z) :
    -chainRadialConstant M N ≤ inner ℝ g z := by
  rw [chainMajorant_subdifferential hN] at hg
  have hconv : Convex ℝ {v : ChainSpace M N | -chainRadialConstant M N ≤ inner ℝ v z} := by
    intro u hu v hv a b ha hb hab
    change -chainRadialConstant M N ≤ _ at hu hv ⊢
    simp only [inner_add_left, real_inner_smul_left]
    have hau := mul_le_mul_of_nonneg_left hu ha
    have hbv := mul_le_mul_of_nonneg_left hv hb
    have hsum : (a + b) * (-chainRadialConstant M N) = -chainRadialConstant M N := by rw [hab, one_mul]
    nlinarith
  apply convexHull_min (t := {v : ChainSpace M N | -chainRadialConstant M N ≤ inner ℝ v z}) ?_ hconv hg
  rintro v ⟨y, hy, hv⟩
  exact chain_source_radial_inner_lower hN hy hv

end WC
