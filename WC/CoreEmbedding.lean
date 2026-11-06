import WC.Rotation
import WC.Construction
import WC.Isometry
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fin.Basic

/-! Concrete core labels, their orthonormal embedding, and continuous
relabeling of ambient prefixes back to the chain coordinates. -/

noncomputable section
namespace WC
open scoped Classical

def coreEmbedding (M N d : ℕ) (hd : M * N ≤ d) : Fin M × Fin N ↪ Fin d :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hd)

variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def orthonormalSynthesis (u : ι → E) (hu : Orthonormal ℝ u) : EuclideanSpace ℝ ι →ₗᵢ[ℝ] E := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let L := b.constr ℝ u
  have hL : L ∘ b = u := by
    funext i
    exact b.constr_basis ℝ u i
  exact L.isometryOfOrthonormal (v := b) (EuclideanSpace.basisFun ι ℝ).orthonormal
    (by rw [hL]; exact hu)

@[simp] theorem orthonormalSynthesis_basis (u : ι → E) (hu : Orthonormal ℝ u) (i : ι) :
    orthonormalSynthesis u hu (EuclideanSpace.basisFun ι ℝ i) = u i := by
  exact (EuclideanSpace.basisFun ι ℝ).toBasis.constr_basis ℝ u i

def coordinateEmbedding (e : ι ↪ κ) : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
  orthonormalSynthesis (fun i => EuclideanSpace.basisFun κ ℝ (e i))
    ((EuclideanSpace.basisFun κ ℝ).orthonormal.comp e e.injective)

def relabelPrefix (e : ι ↪ κ) (s : Finset ι)
    (p : {u : {j // j ∈ s.image e} → E // Orthonormal ℝ u}) :
    {u : {i // i ∈ s} → E // Orthonormal ℝ u} :=
  ⟨fun i => p.val ⟨e i.val, Finset.mem_image_of_mem e i.property⟩,
    p.property.comp (fun i => ⟨e i.val, Finset.mem_image_of_mem e i.property⟩)
      (fun i j hij => Subtype.ext (e.injective (congrArg Subtype.val hij)))⟩

theorem relabelPrefix_continuous (e : ι ↪ κ) (s : Finset ι) :
    Continuous (relabelPrefix (E := E) e s) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  exact (continuous_apply (⟨e i.val, Finset.mem_image_of_mem e i.property⟩ :
    {j // j ∈ s.image e})).comp continuous_subtype_val

variable [CompleteSpace E]

theorem orthonormalSynthesis_projection (u : ι → E) (hu : Orthonormal ℝ u) (x : E) (i : ι) :
    isometryProjection (orthonormalSynthesis u hu) x i = inner ℝ (u i) x := by
  have h := (orthonormalSynthesis u hu).toContinuousLinearMap.adjoint_inner_right
    (EuclideanSpace.basisFun ι ℝ i) x
  change inner ℝ (EuclideanSpace.basisFun ι ℝ i)
      (isometryProjection (orthonormalSynthesis u hu) x) =
    inner ℝ (orthonormalSynthesis u hu (EuclideanSpace.basisFun ι ℝ i)) x at h
  rwa [EuclideanSpace.basisFun_inner, orthonormalSynthesis_basis] at h

def rotatedCore {d : ℕ} (e : ι ↪ Fin d) (g : Frame.Orthogonal (Rotation.Normalized.Ambient d)) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] Rotation.Normalized.Ambient d :=
  (Frame.act _ g).toLinearIsometry.comp (coordinateEmbedding e)

@[simp] theorem rotatedCore_basis {d : ℕ} (e : ι ↪ Fin d)
    (g : Frame.Orthogonal (Rotation.Normalized.Ambient d)) (i : ι) :
    rotatedCore e g (EuclideanSpace.basisFun ι ℝ i) = Rotation.Normalized.coordinates g (e i) := by
  change Frame.act _ g ((coordinateEmbedding e) (EuclideanSpace.basisFun ι ℝ i)) = _
  have he : coordinateEmbedding e (EuclideanSpace.basisFun ι ℝ i) =
      EuclideanSpace.basisFun (Fin d) ℝ (e i) := orthonormalSynthesis_basis _ _ i
  rw [he]
  rfl

theorem rotatedCore_projection_coordinate {d : ℕ} (e : ι ↪ Fin d)
    (g : Frame.Orthogonal (Rotation.Normalized.Ambient d)) (x : Rotation.Normalized.Ambient d) (i : ι) :
    isometryProjection (rotatedCore e g) x i = inner ℝ (Rotation.Normalized.coordinates g (e i)) x := by
  have h := (rotatedCore e g).toContinuousLinearMap.adjoint_inner_right
    (EuclideanSpace.basisFun ι ℝ i) x
  change inner ℝ (EuclideanSpace.basisFun ι ℝ i)
      (isometryProjection (rotatedCore e g) x) =
    inner ℝ (rotatedCore e g (EuclideanSpace.basisFun ι ℝ i)) x at h
  rwa [EuclideanSpace.basisFun_inner, rotatedCore_basis] at h

theorem rotatedCore_projection {d : ℕ} (e : ι ↪ Fin d)
    (g : Frame.Orthogonal (Rotation.Normalized.Ambient d)) (x : Rotation.Normalized.Ambient d) :
    isometryProjection (rotatedCore e g) x = isometryProjection (coordinateEmbedding e)
      (isometryProjection (Frame.act _ g).toLinearIsometry x) := by
  change (((Frame.act _ g).toContinuousLinearMap.comp (coordinateEmbedding e).toContinuousLinearMap).adjoint) x = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

end WC
