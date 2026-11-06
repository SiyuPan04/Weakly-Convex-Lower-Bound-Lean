import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The convex hull of a compact set in finite dimension is compact.
The proof uses the actual Carathéodory theorem and compact standard simplices. -/

noncomputable section
namespace WC

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def convexSumPiece (s : Set E) (k : ℕ) : Set E :=
  (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin k) ×ˢ Set.pi Set.univ (fun _ : Fin k => s))

theorem convexSumPiece_compact {s : Set E} (hs : IsCompact s) (k : ℕ) :
    IsCompact (convexSumPiece s k) := by
  have hpi : IsCompact (Set.pi Set.univ (fun _ : Fin k => s)) :=
    isCompact_univ_pi (fun _ => hs)
  apply ((isCompact_stdSimplex ℝ (Fin k)).prod hpi).image
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_apply i).comp continuous_fst |>.smul ((continuous_apply i).comp continuous_snd))

theorem convexSumPiece_subset (s : Set E) (k : ℕ) :
    convexSumPiece s k ⊆ convexHull ℝ s := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
    (fun i => hz i (Set.mem_univ _)) rfl

theorem convexHull_eq_bounded_convexSums (s : Set E) :
    convexHull ℝ s = ⋃ k : Fin (Module.finrank ℝ E + 2), convexSumPiece s k.val := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, hι, z, w, hz, hind, hwpos, hwsum, hsum⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    letI := hι
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
      hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    let k : Fin (Module.finrank ℝ E + 2) := ⟨Fintype.card ι, by omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    refine ⟨((fun j => w (e.symm j)), (fun j => z (e.symm j))), ⟨?_, ?_⟩, ?_⟩
    · refine ⟨fun j => (hwpos _).le, ?_⟩
      exact (e.symm.sum_comp w).trans hwsum
    · intro j _
      exact hz (Set.mem_range_self _)
    · exact (e.symm.sum_comp (fun i => w i • z i)).trans hsum
  · apply Set.iUnion_subset
    intro k
    exact convexSumPiece_subset s k.val

theorem compact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [convexHull_eq_bounded_convexSums]
  exact isCompact_iUnion (fun k => convexSumPiece_compact hs k.val)

theorem closedConvexHull_eq_convexHull_of_compact {s : Set E} (hs : IsCompact s) :
    closedConvexHull ℝ s = convexHull ℝ s := by
  rw [closedConvexHull_eq_closure_convexHull, (compact_convexHull hs).isClosed.closure_eq]

end WC
