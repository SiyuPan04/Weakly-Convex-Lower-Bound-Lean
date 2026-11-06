import WC.DiagonalLocality
import WC.SubgradientConstancy
import WC.SubgradientCalculus

/-! Genuine value and full-subdifferential locality of the least
Lipschitz majorant on the robust diagonal tube. -/

noncomputable section
namespace WC
open scoped BigOperators Classical
open Filter Topology

theorem fullOracle_congr_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    {G₁ G₂ ρ₁ ρ₂ : ℝ} {f g : E → ℝ} (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hfLip : GloballyLipschitz G₁ f) (hgLip : GloballyLipschitz G₂ g)
    (hfWC : WeaklyConvex ρ₁ f) (hgWC : WeaklyConvex ρ₂ g)
    (x : E) (heq : f =ᶠ[𝓝 x] g) :
    fullOracle hG₁ hρ₁ hfLip hfWC x = fullOracle hG₂ hρ₂ hgLip hgWC x := by
  apply Prod.ext heq.eq_of_nhds
  apply Subtype.ext
  apply TopologicalSpace.NonemptyCompacts.ext
  ext v
  exact frechetSubgradient_congr_eventuallyEq heq

theorem chainMajorant_diagonalMask_eq {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (x : ChainSpace M N) (r : ℕ)
    (hidden : ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) →
      |x i| ≤ robustTolerance M N) :
    chainMajorant x = chainMajorant (diagonalMask M N (r + 1) x) := by
  have hNpos : 0 < N := by omega
  apply constant_on_segment_of_subgradient_inner_zero (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_lipschitz hNpos)
    (chainMajorant_weaklyConvex hNpos) x (diagonalMask M N (r + 1) x)
  intro t ht v hv
  have hpath : ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) →
      |(x + t • (diagonalMask M N (r + 1) x - x)) i| ≤ robustTolerance M N := by
    intro i hi
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, diagonalMask_apply]
    by_cases hkeep : diagonalLevel N (i.1.val, i.2.val) < r + 1
    · rw [if_pos hkeep, sub_self, mul_zero, add_zero]
      exact hidden i hi
    · rw [if_neg hkeep]
      have heq : x i + t * (0 - x i) = (1 - t) * x i := by ring
      rw [heq, abs_mul, abs_of_nonneg (by linarith [ht.2])]
      have hh := hidden i hi
      nlinarith [abs_nonneg (x i), ht.1, ht.2]
  apply diagonalMask_inner_sub_zero x v
  intro i hi
  exact chainMajorant_subgradient_diagonal_zero hM hN _ r hpath hv i (by omega)

def diagonalTube (M N r : ℕ) : Set (ChainSpace M N) :=
  {x | ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) →
    |x i| < robustTolerance M N}

theorem diagonalTube_isOpen (M N r : ℕ) : IsOpen (diagonalTube M N r) := by
  have heq : diagonalTube M N r = ⋂ i : Fin M × Fin N,
      {x : ChainSpace M N | r ≤ diagonalLevel N (i.1.val, i.2.val) → |x i| < robustTolerance M N} := by
    ext x
    simp [diagonalTube]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : r ≤ diagonalLevel N (i.1.val, i.2.val)
  · simpa only [hi, true_implies] using
      isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin M × Fin N => ℝ) i).abs continuous_const
  · simp [hi]

theorem chainMajorant_diagonalMask_eventuallyEq {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (x : ChainSpace M N) (r : ℕ) (hidden : x ∈ diagonalTube M N r) :
    chainMajorant (M := M) (N := N) =ᶠ[𝓝 x]
      (fun y => chainMajorant (diagonalMask M N (r + 1) y)) := by
  filter_upwards [(diagonalTube_isOpen M N r).mem_nhds hidden] with y hy
  exact chainMajorant_diagonalMask_eq hM hN y r (fun i hi => (hy i hi).le)

theorem chainMajorant_diagonalMask_subdifferential {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (x : ChainSpace M N) (r : ℕ) (hidden : x ∈ diagonalTube M N r) :
    subdifferential chainMajorant x =
      subdifferential (fun y => chainMajorant (diagonalMask M N (r + 1) y)) x := by
  ext v
  exact frechetSubgradient_congr_eventuallyEq (chainMajorant_diagonalMask_eventuallyEq hM hN x r hidden)

end WC
