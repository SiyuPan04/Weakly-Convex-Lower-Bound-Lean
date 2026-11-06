import WC.CoreEmbedding
import WC.Numerics

/-! The actual ambient coordinate filtration and its finite combinatorics. -/

noncomputable section
namespace WC
open scoped Classical

def coreLabels {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) : Finset (Fin d) := Finset.univ.image e

def diagonalExposed {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) (t : ℕ) : Finset (Fin d) :=
  (exposedIndices M N (t + 1)).image e

theorem coreLabels_card {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) :
    (coreLabels e).card = M * N := by
  simp [coreLabels, Finset.card_image_of_injective _ e.injective]

theorem diagonalExposed_mono {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) : Monotone (diagonalExposed e) := by
  intro s t hst
  exact Finset.image_mono e (exposedIndices_mono M N (Nat.add_le_add_right hst 1))

theorem diagonalExposed_subset {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d) (t : ℕ) :
    diagonalExposed e t ⊆ coreLabels e :=
  Finset.image_mono e (Finset.subset_univ _)

theorem diagonalExposed_proper {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hM : 0 < M) (hN : 0 < N) {t : ℕ} (ht : t < (M - 1) * stagger N) :
    diagonalExposed e t ≠ coreLabels e := by
  let i : Fin M × Fin N := (⟨M - 1, by omega⟩, ⟨0, hN⟩)
  have hi : i ∉ exposedIndices M N (t + 1) := by
    intro h
    exact last_block_unexposed hM i.2
      (exposedIndices_mono M N (by omega : t + 1 ≤ (M - 1) * stagger N) h)
  intro heq
  have hmem : e i ∈ coreLabels e := Finset.mem_image_of_mem e (Finset.mem_univ i)
  rw [← heq] at hmem
  obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hmem
  exact hi ((e.injective hij) ▸ hj)

theorem diagonalExposed_width {M N d : ℕ} (e : Fin M × Fin N ↪ Fin d)
    (hN : 256 ≤ N) (t : ℕ) :
    (diagonalExposed e t \ Rotation.Normalized.previous (diagonalExposed e) t).card ≤ 5 := by
  cases t with
  | zero =>
    simp only [Rotation.Normalized.previous, Finset.sdiff_empty]
    have h := exposedIndices_step_card M N 0 hN
    rw [exposedIndices_zero, Finset.sdiff_empty] at h
    exact Finset.card_image_le.trans h
  | succ t =>
    change ((exposedIndices M N (t + 1 + 1)).image e \ (exposedIndices M N (t + 1)).image e).card ≤ 5
    rw [← Finset.image_sdiff _ _ e.injective]
    exact Finset.card_image_le.trans (exposedIndices_step_card M N (t + 1) hN)

theorem diagonal_horizon_positive {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    0 < (M - 1) * stagger N := Nat.mul_pos (by omega) (stagger_pos hN)

def terminalBlock {M N : ℕ} (hM : 0 < M) : Finset (Fin M × Fin N) :=
  Finset.univ.image (fun n : Fin N => (⟨M - 1, by omega⟩, n))

theorem terminalBlock_card {M N : ℕ} (hM : 0 < M) : (terminalBlock (N := N) hM).card = N := by
  rw [terminalBlock, Finset.card_image_of_injective]
  · exact Finset.card_fin N
  · intro i j hij
    exact Prod.mk.inj hij |>.2

theorem terminalBlock_hidden {M N : ℕ} (hM : 0 < M) {i : Fin M × Fin N}
    (hi : i ∈ terminalBlock (N := N) hM) : i ∉ exposedIndices M N ((M - 1) * stagger N) := by
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hi
  exact last_block_unexposed hM n

end WC
