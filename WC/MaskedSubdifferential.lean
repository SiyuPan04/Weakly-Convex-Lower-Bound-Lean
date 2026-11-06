import WC.MaskedLocality

/-! Literal equality of the complete majorant subdifferential at a
robust query and at its prefix projection. -/

noncomputable section
namespace WC
open scoped Classical

theorem FrechetSubgradient.of_equal_translated_increments {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → ℝ} {x y v : E} (hv : FrechetSubgradient f x v)
    (heq : ∀ h : E, f (x + h) - f x = g (y + h) - g y) :
    FrechetSubgradient g y v := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := hv ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hs' := hs (x + (z - y)) (by simpa only [add_sub_cancel_left] using hz)
  have ht := heq (z - y)
  rw [add_sub_cancel] at ht
  simp only [add_sub_cancel_left] at hs'
  linarith

theorem frechetSubgradient_comp_idempotent_basepoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (P : E →ₗ[ℝ] E) (hP : ∀ x, P (P x) = P x) (x v : E) :
    FrechetSubgradient (fun y => f (P y)) x v ↔
      FrechetSubgradient (fun y => f (P y)) (P x) v := by
  have hinc (h : E) : f (P (x + h)) - f (P x) = f (P (P x + h)) - f (P (P x)) := by
    rw [map_add, map_add, hP]
  exact ⟨fun hv => hv.of_equal_translated_increments hinc,
    fun hv => hv.of_equal_translated_increments (fun h => (hinc h).symm)⟩

def diagonalMaskLinear (M N r : ℕ) : ChainSpace M N →ₗ[ℝ] ChainSpace M N where
  toFun := diagonalMask M N r
  map_add' x y := by
    apply PiLp.ext
    intro i
    simp only [diagonalMask_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    apply PiLp.ext
    intro i
    simp only [diagonalMask_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem diagonalMask_mem_diagonalTube {M N r : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (hidden : x ∈ diagonalTube M N r) :
    diagonalMask M N (r + 1) x ∈ diagonalTube M N r := by
  intro i hi
  rw [diagonalMask_apply]
  split_ifs
  · exact hidden i hi
  · simpa only [abs_zero] using robustTolerance_pos M hN

/-- Equality of the entire actual Fréchet subdifferential at the query
and at its next-diagonal prefix projection, as stated in the manuscript. -/
theorem chainMajorant_diagonalMask_subdifferential_eq {M N : ℕ}
    (hM : 1 ≤ M) (hN : 256 ≤ N) (x : ChainSpace M N) (r : ℕ)
    (hidden : x ∈ diagonalTube M N r) :
    subdifferential chainMajorant x =
      subdifferential chainMajorant (diagonalMask M N (r + 1) x) := by
  have hmask := diagonalMask_mem_diagonalTube (by omega : 0 < N) x hidden
  rw [chainMajorant_diagonalMask_subdifferential hM hN x r hidden,
    chainMajorant_diagonalMask_subdifferential hM hN (diagonalMask M N (r + 1) x) r hmask]
  ext v
  exact frechetSubgradient_comp_idempotent_basepoint chainMajorant (diagonalMaskLinear M N (r + 1))
    (diagonalMask_idempotent (r := r + 1)) x v

end WC
