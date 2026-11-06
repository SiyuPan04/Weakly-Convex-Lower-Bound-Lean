import WC.Frame
import WC.Isometry
import WC.OracleImages
import WC.ModelMeasurability

/-! Joint measurability of the complete oracle and continuity of the
actual Moreau gradient under orthogonal rotation. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem rotationProjection_continuous : Continuous (fun p : Frame.Orthogonal E × E =>
    isometryProjection (Frame.act E p.1).toLinearIsometry p.2) := by
  change Continuous (fun p : Frame.Orthogonal E × E =>
    ((p.1 : E →L[ℝ] E).adjoint) p.2)
  exact ((ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E)).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd

theorem rotationAction_continuous : Continuous (fun p : Frame.Orthogonal E × E =>
    Frame.act E p.1 p.2) := by
  exact (continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd

theorem rotated_fullOracle {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (g : Frame.Orthogonal E) (x : E) :
    fullOracle hG hρ (isometricLift_lipschitz (Frame.act E g).toLinearIsometry hG hlip)
      (isometricLift_weaklyConvex (Frame.act E g).toLinearIsometry hρ hwc) x =
    (f (isometryProjection (Frame.act E g).toLinearIsometry x),
      compactConvexImage (g : E →L[ℝ] E)
        (fullSubdifferential hG hρ hlip hwc
          (isometryProjection (Frame.act E g).toLinearIsometry x))) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply TopologicalSpace.NonemptyCompacts.ext
    exact frechetSubdifferential_isometricLift x (Frame.act E g).toLinearIsometry hρ hwc

variable [MeasurableSpace E] [BorelSpace E]

theorem rotated_fullOracle_measurable {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) :
    Measurable (fun p : Frame.Orthogonal E × E =>
      fullOracle hG hρ (isometricLift_lipschitz (Frame.act E p.1).toLinearIsometry hG hlip)
        (isometricLift_weaklyConvex (Frame.act E p.1).toLinearIsometry hρ hwc) p.2) := by
  letI : MeasurableSpace (E →L[ℝ] E) := borel _
  letI : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
  have hproj := rotationProjection_continuous (E := E)
  have hvalue := (hlip.continuous hG).measurable.comp hproj.measurable
  have hset := (fullSubdifferential_measurable hG hρ hlip hwc).comp hproj.measurable
  have himage := (compactConvexImage_continuous (E := E) (F := E)).measurable.comp
    ((continuous_subtype_val.comp continuous_fst).measurable.prodMk hset)
  have h := hvalue.prodMk himage
  convert h using 1
  funext p
  exact rotated_fullOracle hG hρ hlip hwc p.1 p.2

theorem rotated_moreau_gradient_continuous {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) :
    Continuous (fun p : Frame.Orthogonal E × E =>
      gradient (moreauEnvelope (1 / (2 * ρ))
        (isometricLift (Frame.act E p.1).toLinearIsometry f)) p.2) := by
  have hgrad := (moreau_gradient_continuous hG hρ hlip hwc).comp
    (rotationProjection_continuous (E := E))
  have h := (continuous_subtype_val.comp continuous_fst).clm_apply hgrad
  convert h using 1
  funext p
  exact moreau_gradient_isometricLift (Frame.act E p.1).toLinearIsometry hG hρ hlip hwc p.2

end WC
