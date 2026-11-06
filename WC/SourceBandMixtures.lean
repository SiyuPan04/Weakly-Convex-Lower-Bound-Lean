import WC.SourceBandGeometry

/-! Every convex mixture in one actual remote-source radius band is separated
from zero. Pairwise inner products are proved, not assumed for the construction. -/

noncomputable section
namespace WC

open scoped BigOperators

theorem convex_mixture_norm_sq_ge {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (w : ι → ℝ) (g : ι → E) (a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hpair : ∀ i j, a ≤ inner ℝ (g i) (g j)) :
    a ≤ ‖∑ i, w i • g i‖ ^ 2 := by
  have hrow (i : ι) : a ≤ ∑ j, w j * inner ℝ (g i) (g j) := by
    calc
      a = ∑ j, w j * a := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ j, w j * inner ℝ (g i) (g j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpair i j) (hw j))
  have hnorm : ‖∑ i, w i • g i‖ ^ 2 =
      ∑ i, w i * (∑ j, w j * inner ℝ (g i) (g j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Finset.mul_sum, mul_assoc]
    simp only [real_inner_comm]
  rw [hnorm]
  calc
    a = ∑ i, w i * a := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, w i * (∑ j, w j * inner ℝ (g i) (g j)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw i))

theorem remote_source_band_mixture {M N : ℕ} {ι : Type*} [Fintype ι]
    (hN : 256 ≤ N) {z : ChainSpace M N} {a : ℝ} (ha : 0 < a)
    (w : ι → ℝ) (y g : ι → ChainSpace M N)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hsource : ∀ i, y i ∈ majorantSources coupledFunction 2 z)
    (hgradient : ∀ i, g i ∈ subdifferential coupledFunction (y i))
    (hrange : ∀ i, a < ‖z - y i‖ ∧ ‖z - y i‖ ≤ 8 * a) :
    (1 / 8 : ℝ) ≤ ‖∑ i, w i • g i‖ ^ 2 := by
  apply convex_mixture_norm_sq_ge w g (1 / 8) hw hsum
  intro i j
  have hi : z ≠ y i := sub_ne_zero.mp (norm_pos_iff.mp (ha.trans (hrange i).1))
  have hj : z ≠ y j := sub_ne_zero.mp (norm_pos_iff.mp (ha.trans (hrange j).1))
  by_cases hij : ‖z - y i‖ ≤ ‖z - y j‖
  · exact (chain_remote_sources_inner_gt hN (hsource i) (hsource j) hi hj
      (hgradient i) (hgradient j) hij (by nlinarith [(hrange i).1, (hrange j).2])).le
  · have hji := (le_of_not_ge hij)
    have h := chain_remote_sources_inner_gt hN (hsource j) (hsource i) hj hi
      (hgradient j) (hgradient i) hji (by nlinarith [(hrange j).1, (hrange i).2])
    simpa only [real_inner_comm] using h.le

end WC
