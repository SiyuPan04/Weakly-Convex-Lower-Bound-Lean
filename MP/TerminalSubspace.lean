import MP.Construction
import WC.DiagonalSubspaces

/-! The literal terminal-subspace clause of Proposition
`prop:terminal-stationarity`, derived from the proved robust tube bound. -/

noncomputable section
namespace MP
open WC
open scoped Classical

theorem zero_outside_of_mem_coordinateSpan {ι : Type*} [Fintype ι]
    (s : Finset ι) (x : EuclideanSpace ℝ ι) (hx : x ∈ coordinateSpan s)
    (i : ι) (hi : i ∉ s) : x i = 0 := by
  have hle : coordinateSpan s ≤ (EuclideanSpace.projₗ i).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change EuclideanSpace.basisFun ι ℝ j i = 0
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [EuclideanSpace.basisFun_apply, hji]
  exact hle hx

theorem terminal_subspace_barrier {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (x : ChainSpace M N)
    (hx : x ∈ coordinateSpan (exposedIndices M N ((M - 1) * stagger N))) :
    1 / (10 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 9) chainMajorant) x‖ := by
  apply terminal_diagonal_barrier hM hN hMmax x
  intro i hi
  have hnot : i ∉ exposedIndices M N ((M - 1) * stagger N) := by
    simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [zero_outside_of_mem_coordinateSpan _ x hx i hnot, abs_zero]
  exact robustTolerance_pos M (by omega)

/-- Both cases, with the horizon, exactly as in the displayed proposition. -/
theorem terminal_stationarity {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) :
    M * N ≤ 16 * ((M - 1) * stagger N) ∧
      (∀ x ∈ coordinateSpan (exposedIndices M N ((M - 1) * stagger N)),
        1 / (10 * Real.sqrt (N : ℝ)) < ‖gradient (moreauEnvelope (1 / 9) chainMajorant) x‖) ∧
      (∀ x : ChainSpace M N, x ∈ diagonalTube M N ((M - 1) * stagger N) →
        1 / (10 * Real.sqrt (N : ℝ)) < ‖gradient (moreauEnvelope (1 / 9) chainMajorant) x‖) :=
  ⟨WC.horizon_bound hM hN, terminal_subspace_barrier hM hN hMmax,
    terminal_diagonal_barrier hM hN hMmax⟩

end MP
