import WC.ChainSources
import WC.MaskedSubdifferential
import WC.DiagonalSubspaces

/-! Literal source order and the complete robust zero-chain identity for
the MP submission. The natural index r denotes the paper's time r-1. -/

noncomputable section
namespace MP
open WC
open scoped BigOperators Classical

theorem source_order {M N : ℕ} (hN : 0 < N) {z y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 z) : ∀ i, y i ≤ z i :=
  chain_source_coord_le hN hy

theorem remote_source_subdifferential {M N : ℕ} (hN : 0 < N) {z y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 z) (hzy : z ≠ y) :
    subdifferential coupledFunction y = {(-2 / ‖z - y‖) • (z - y)} := by
  ext v
  constructor
  · intro hv
    exact chain_remote_source_subgradient hN hy hzy hv
  · intro hv
    obtain ⟨w, hw⟩ := subdifferential_nonempty y (rawLipschitzConstant_nonneg M N)
      (by norm_num : (0 : ℝ) ≤ 9 / 2)
      (coupledFunction_global_lipschitz hN) (weaklyConvex_coupledFunction hN)
    have heq := chain_remote_source_subgradient hN hy hzy hw
    have hv' : v = (-2 / ‖z - y‖) • (z - y) := hv
    rw [hv', ← heq]
    exact hw

theorem mem_coordinateSpan_of_zero_outside {ι : Type*} [Fintype ι]
    (s : Finset ι) (v : EuclideanSpace ℝ ι) (hv : ∀ i, i ∉ s → v i = 0) :
    v ∈ coordinateSpan s := by
  rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr' v]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ s
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [EuclideanSpace.basisFun_inner, hv i hi, zero_smul]
    exact Submodule.zero_mem _

/-- Proposition `newrand:robust`, with genuine function values and entire
Fréchet subdifferentials, including the basepoint identity. -/
theorem robust_oracle_identity {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (z : ChainSpace M N) (r : ℕ) (hidden : z ∈ diagonalTube M N r) :
    chainMajorant z = chainMajorant (diagonalMask M N (r + 1) z) ∧
    subdifferential chainMajorant z = subdifferential chainMajorant (diagonalMask M N (r + 1) z) ∧
    subdifferential chainMajorant z ⊆ coordinateSpan (exposedIndices M N (r + 1)) := by
  refine ⟨chainMajorant_diagonalMask_eq hM hN z r (fun i hi => (hidden i hi).le),
    chainMajorant_diagonalMask_subdifferential_eq hM hN z r hidden, ?_⟩
  intro v hv
  apply mem_coordinateSpan_of_zero_outside
  intro i hi
  have hlevel : r < diagonalLevel N (i.1.val, i.2.val) := by
    simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  exact chainMajorant_subgradient_diagonal_zero hM hN z r
    (fun i hi => (hidden i hi).le) hv i hlevel

end MP
