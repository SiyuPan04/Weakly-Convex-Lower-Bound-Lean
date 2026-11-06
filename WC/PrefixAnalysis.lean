import WC.LinearContraction
import WC.Isometry
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Zero-filled coordinate analysis on any orthonormal prefix, jointly
continuous in the prefix vectors and query, with norm at most one. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def prefixCoordinates (s : Finset ι) (u : {i // i ∈ s} → E) (x : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ s then inner ℝ (u ⟨i, hi⟩) x else 0)

def prefixAnalysisLinear (s : Finset ι) (u : {i // i ∈ s} → E) : E →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := prefixCoordinates s u
  map_add' x y := by
    ext i
    simp only [prefixCoordinates, PiLp.toLp_apply, PiLp.add_apply]
    split <;> simp_all [inner_add_right]
  map_smul' a x := by
    ext i
    simp only [prefixCoordinates, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    split <;> simp_all [real_inner_smul_right]

theorem prefixCoordinates_norm_sq (s : Finset ι) (u : {i // i ∈ s} → E) (x : E) :
    ‖prefixCoordinates s u x‖ ^ 2 = ∑ i : {i // i ∈ s}, (inner ℝ (u i) x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have heq : (∑ i, (prefixCoordinates s u x i) ^ 2) =
      ∑ i ∈ s, (prefixCoordinates s u x i) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    simp [prefixCoordinates, hi]
  rw [heq, Finset.sum_subtype s (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp [prefixCoordinates, i.property]

theorem prefixCoordinates_norm_le (s : Finset ι) (u : {i // i ∈ s} → E)
    (hu : Orthonormal ℝ u) (x : E) : ‖prefixCoordinates s u x‖ ≤ ‖x‖ := by
  have h := hu.sum_inner_products_le (s := Finset.univ) x
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [← prefixCoordinates_norm_sq s u x] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem prefixCoordinates_continuous (s : Finset ι) :
    Continuous (fun p : ({i // i ∈ s} → E) × E => prefixCoordinates s p.1 p.2) := by
  change Continuous (fun p : ({i // i ∈ s} → E) × E => WithLp.toLp 2
    (fun i => if hi : i ∈ s then inner ℝ (p.1 ⟨i, hi⟩) p.2 else 0))
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [prefixCoordinates, dif_pos hi] using
      ((continuous_apply (⟨i, hi⟩ : {i // i ∈ s})).comp continuous_fst).inner continuous_snd
  · simpa only [prefixCoordinates, dif_neg hi] using
      (continuous_const : Continuous (fun _ : ({i // i ∈ s} → E) × E => (0 : ℝ)))

end WC
