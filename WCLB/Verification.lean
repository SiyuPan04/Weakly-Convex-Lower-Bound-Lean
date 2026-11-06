import WCLB.Conditions
import WCLB.Construction

/-! Concrete verification of all four unscaled conditions. -/

namespace WCLB

theorem construction_satisfies_conditions {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) :
    UnscaledHardInstanceConditions M N ((M - 1) * WC.stagger N)
      WC.chainMajorant (WC.exposedIndices M N) := by
  apply chainMajorant_conditions_of_terminal hM hN
  intro x hx
  apply terminal_diagonal_barrier hM hN hMmax x
  intro i hi
  apply hx
  simp only [WC.exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

end WCLB
