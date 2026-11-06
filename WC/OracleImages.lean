import WC.Oracle
import Mathlib.Topology.Sets.VietorisTopology

/-! Continuous linear images in the actual compact-convex oracle space,
jointly in the linear map and the set. -/

noncomputable section
namespace WC

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compactConvexImage (L : E →L[ℝ] F) (S : CompactConvexSets E) : CompactConvexSets F :=
  ⟨S.val.map L L.continuous, S.property.linear_image L.toLinearMap⟩

@[simp] theorem compactConvexImage_coe (L : E →L[ℝ] F) (S : CompactConvexSets E) :
    ((compactConvexImage L S).val : Set F) = L '' (S.val : Set E) := rfl

theorem compactConvexImage_continuous :
    Continuous (fun p : (E →L[ℝ] F) × CompactConvexSets E => compactConvexImage p.1 p.2) := by
  apply continuous_induced_rng.mpr
  have hS : Continuous (fun p : (E →L[ℝ] F) × CompactConvexSets E => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact hS.nonemptyCompacts_map' (continuous_fst.fst.clm_apply continuous_snd)

theorem compactConvexImage_measurable [SecondCountableTopology (E →L[ℝ] F)]
    [SecondCountableTopology (CompactConvexSets E)] :
    @Measurable _ _ (borel _) (borel _)
      (fun p : (E →L[ℝ] F) × CompactConvexSets E => compactConvexImage p.1 p.2) :=
  compactConvexImage_continuous.borel_measurable

end WC
