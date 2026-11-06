import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum

/-!
# Dimensions of the unrevealed frame complement
-/

noncomputable section
namespace WC
namespace FrameGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {d : ℕ}

def exposedSpan (b : OrthonormalBasis (Fin d) ℝ E) (I : Finset (Fin d)) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (I : Set (Fin d)))

omit [FiniteDimensional ℝ E] in
theorem finrank_exposedSpan_le (b : OrthonormalBasis (Fin d) ℝ E) (I : Finset (Fin d)) :
    Module.finrank ℝ (exposedSpan b I) ≤ I.card := by
  classical
  have heq : b '' (I : Set (Fin d)) = ((I.image b : Finset E) : Set E) := by simp
  unfold exposedSpan
  rw [heq]
  exact (finrank_span_finset_le_card (R := ℝ) (I.image b)).trans Finset.card_image_le

omit [FiniteDimensional ℝ E] in
theorem mem_orthogonal_of_not_mem (b : OrthonormalBasis (Fin d) ℝ E)
    (I : Finset (Fin d)) (j : Fin d) (hj : j ∉ I) : b j ∈ (exposedSpan b I)ᗮ := by
  have hle : exposedSpan b I ≤ (innerSL ℝ (b j)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change inner ℝ (b j) (b i) = 0
    apply b.orthonormal.inner_eq_zero
    intro h
    subst i
    exact hj hi
  apply (exposedSpan b I).mem_orthogonal' (b j) |>.mpr
  intro u hu
  exact hle hu

omit [FiniteDimensional ℝ E] in
theorem finrank_ambient (b : OrthonormalBasis (Fin d) ℝ E) : Module.finrank ℝ E = d := by
  simpa using Module.finrank_eq_card_basis b.toBasis

theorem finrank_complement (b : OrthonormalBasis (Fin d) ℝ E) (I : Finset (Fin d)) :
    Module.finrank ℝ (exposedSpan b I)ᗮ = d - Module.finrank ℝ (exposedSpan b I) := by
  have hadd := (exposedSpan b I).finrank_add_finrank_orthogonal
  rw [finrank_ambient b] at hadd
  omega

theorem finrank_complement_ge (b : OrthonormalBasis (Fin d) ℝ E)
    (I : Finset (Fin d)) {K : ℕ} (hcard : I.card ≤ K) :
    d - K ≤ Module.finrank ℝ (exposedSpan b I)ᗮ := by
  have hspan := finrank_exposedSpan_le b I
  rw [finrank_complement b I]
  omega

theorem complement_nontrivial (b : OrthonormalBasis (Fin d) ℝ E)
    (I : Finset (Fin d)) {K : ℕ} (hcard : I.card ≤ K) (hd : K + 2 ≤ d) :
    Nontrivial (exposedSpan b I)ᗮ := by
  apply (Module.finrank_pos_iff (R := ℝ)).mp
  have hge := finrank_complement_ge b I hcard
  omega

theorem finrank_complement_ge_real (b : OrthonormalBasis (Fin d) ℝ E)
    (I : Finset (Fin d)) {K : ℕ} (hcard : I.card ≤ K) (hd : K ≤ d) :
    (d : ℝ) - K ≤ (Module.finrank ℝ (exposedSpan b I)ᗮ : ℝ) := by
  have h := finrank_complement_ge b I hcard
  have hcast : ((d - K : ℕ) : ℝ) ≤ (Module.finrank ℝ (exposedSpan b I)ᗮ : ℝ) := by
    exact_mod_cast h
  simpa only [Nat.cast_sub hd] using hcast

def hiddenVector (b : OrthonormalBasis (Fin d) ℝ E) (I : Finset (Fin d))
    (j : Fin d) (hj : j ∉ I) : (exposedSpan b I)ᗮ :=
  ⟨b j, mem_orthogonal_of_not_mem b I j hj⟩

omit [FiniteDimensional ℝ E] in
theorem hiddenVector_unit (b : OrthonormalBasis (Fin d) ℝ E) (I : Finset (Fin d))
    (j : Fin d) (hj : j ∉ I) : ‖hiddenVector b I j hj‖ = 1 := by
  exact b.orthonormal.norm_eq_one j

end FrameGeometry
end WC
