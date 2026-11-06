import WC.Numerics
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Literal subspace direct-sum and quotient-dimension statements for
the manuscript's diagonal coordinate filtration, including its first layer. -/

noncomputable section
namespace WC
open scoped Classical

def coordinateSpan {ι : Type*} [Fintype ι] (s : Finset ι) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  Submodule.span ℝ ((EuclideanSpace.basisFun ι ℝ) '' (s : Set ι))

theorem coordinateSpan_finrank {ι : Type*} [Fintype ι] (s : Finset ι) :
    Module.finrank ℝ (coordinateSpan s) = s.card := by
  let u : {i // i ∈ s} → EuclideanSpace ℝ ι := fun i => EuclideanSpace.basisFun ι ℝ i.val
  have hlin : LinearIndependent ℝ u :=
    ((EuclideanSpace.basisFun ι ℝ).orthonormal.comp (fun i : {i // i ∈ s} => i.val)
      Subtype.val_injective).linearIndependent
  have heq : Set.range u = (EuclideanSpace.basisFun ι ℝ) '' (s : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  unfold coordinateSpan
  rw [← heq]
  simpa only [Fintype.card_coe] using finrank_span_eq_card hlin

theorem coordinateSpan_mono {ι : Type*} [Fintype ι] {s t : Finset ι} (hst : s ⊆ t) :
    coordinateSpan s ≤ coordinateSpan t :=
  Submodule.span_mono (Set.image_mono hst)

theorem coordinateSpan_disjoint {ι : Type*} [Fintype ι] {s t : Finset ι} (hst : Disjoint s t) :
    Disjoint (coordinateSpan s) (coordinateSpan t) := by
  apply (EuclideanSpace.basisFun ι ℝ).orthonormal.linearIndependent.disjoint_span_image
  exact Finset.disjoint_coe.mpr hst

theorem coordinateSpan_union {ι : Type*} [Fintype ι] [DecidableEq ι] (s t : Finset ι) :
    coordinateSpan (s ∪ t) = coordinateSpan s ⊔ coordinateSpan t := by
  simp only [coordinateSpan, Finset.coe_union, Set.image_union, Submodule.span_union]

def diagonalLayerIndices (M N r : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter (fun i => diagonalLevel N (i.1.val, i.2.val) = r)

def diagonalPreviousSpace (M N r : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin M × Fin N)) :=
  coordinateSpan (exposedIndices M N r)

def diagonalLayerSpace (M N r : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin M × Fin N)) :=
  coordinateSpan (diagonalLayerIndices M N r)

def diagonalNextSpace (M N r : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin M × Fin N)) :=
  coordinateSpan (exposedIndices M N (r + 1))

theorem diagonal_previous_layer_indices_disjoint (M N r : ℕ) :
    Disjoint (exposedIndices M N r) (diagonalLayerIndices M N r) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hlt := (Finset.mem_filter.mp hi).2
  have heq := (Finset.mem_filter.mp hj).2
  omega

theorem diagonal_previous_union_layer (M N r : ℕ) :
    exposedIndices M N r ∪ diagonalLayerIndices M N r = exposedIndices M N (r + 1) := by
  ext i
  simp only [exposedIndices, diagonalLayerIndices, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

/-- The filtration increment is an internal direct sum, including `r=0`
which corresponds to the paper's `t=-1` initial increment. -/
theorem diagonal_subspace_direct_sum (M N r : ℕ) :
    Disjoint (diagonalPreviousSpace M N r) (diagonalLayerSpace M N r) ∧
      diagonalPreviousSpace M N r ⊔ diagonalLayerSpace M N r = diagonalNextSpace M N r := by
  refine ⟨coordinateSpan_disjoint (diagonal_previous_layer_indices_disjoint M N r), ?_⟩
  change coordinateSpan (exposedIndices M N r) ⊔ coordinateSpan (diagonalLayerIndices M N r) = _
  rw [← coordinateSpan_union]
  exact congrArg coordinateSpan (diagonal_previous_union_layer M N r)

theorem diagonal_previous_le_next (M N r : ℕ) :
    diagonalPreviousSpace M N r ≤ diagonalNextSpace M N r :=
  coordinateSpan_mono (exposedIndices_mono M N (Nat.le_succ r))

def diagonalPreviousInNext (M N r : ℕ) : Submodule ℝ (diagonalNextSpace M N r) :=
  (diagonalPreviousSpace M N r).comap (diagonalNextSpace M N r).subtype

/-- The actual quotient of consecutive coordinate subspaces has exactly
the dimension of the new diagonal layer. -/
theorem diagonal_quotient_finrank (M N r : ℕ) :
    Module.finrank ℝ ((diagonalNextSpace M N r) ⧸ diagonalPreviousInNext M N r) =
      Module.finrank ℝ (diagonalLayerSpace M N r) := by
  have hdim := (diagonalPreviousInNext M N r).finrank_quotient_add_finrank
  have heq := (Submodule.comapSubtypeEquivOfLe (diagonal_previous_le_next M N r)).finrank_eq
  change Module.finrank ℝ (diagonalPreviousInNext M N r) =
    Module.finrank ℝ (diagonalPreviousSpace M N r) at heq
  rw [heq] at hdim
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (diagonalPreviousSpace M N r) (diagonalLayerSpace M N r)
  have hdirect := diagonal_subspace_direct_sum M N r
  rw [hdirect.2, hdirect.1.eq_bot, finrank_bot, add_zero] at hsum
  omega

theorem diagonal_layer_finrank_le (M N r : ℕ) (hN : 256 ≤ N) :
    Module.finrank ℝ (diagonalLayerSpace M N r) ≤ 5 := by
  rw [diagonalLayerSpace, coordinateSpan_finrank]
  exact diagonal_width M N r hN

/-- Literal quotient-dimension bound from Lemma `diagonal-width`. -/
theorem diagonal_quotient_finrank_le (M N r : ℕ) (hN : 256 ≤ N) :
    Module.finrank ℝ ((diagonalNextSpace M N r) ⧸ diagonalPreviousInNext M N r) ≤ 5 := by
  rw [diagonal_quotient_finrank]
  exact diagonal_layer_finrank_le M N r hN

@[simp] theorem diagonal_initial_space (M N : ℕ) : diagonalPreviousSpace M N 0 = ⊥ := by
  simp only [diagonalPreviousSpace, exposedIndices_zero, coordinateSpan,
    Finset.coe_empty, Set.image_empty, Submodule.span_empty]

/-- The complete direct-sum and quotient-dimension statement, in zero
based layer notation. -/
theorem diagonal_filtration_width (M N r : ℕ) (hN : 256 ≤ N) :
    Disjoint (diagonalPreviousSpace M N r) (diagonalLayerSpace M N r) ∧
      diagonalPreviousSpace M N r ⊔ diagonalLayerSpace M N r = diagonalNextSpace M N r ∧
      Module.finrank ℝ ((diagonalNextSpace M N r) ⧸ diagonalPreviousInNext M N r) =
        Module.finrank ℝ (diagonalLayerSpace M N r) ∧
      Module.finrank ℝ (diagonalLayerSpace M N r) ≤ 5 :=
  ⟨(diagonal_subspace_direct_sum M N r).1, (diagonal_subspace_direct_sum M N r).2,
    diagonal_quotient_finrank M N r, diagonal_layer_finrank_le M N r hN⟩

end WC
