import WC.CoupledSubgradient

/-! Exact actual subdifferential of each finite affine fan, used to
regroup the smooth-facet formula into the manuscript's block formula. -/

noncomputable section
namespace WC
open scoped Classical

theorem affineFacet_lipschitz (N K m : ℕ) (a : FanFacet N) :
    GloballyLipschitz ((N : ℝ) / 8) (affineFacet N K m a) := by
  have hd (x : EuclideanSpace ℝ (Fin N)) := hasFDerivAt_affineFacet N K m a x
  have hb (x : EuclideanSpace ℝ (Fin N)) :
      ‖fderiv ℝ (affineFacet N K m a) x‖ ≤ (N : ℝ) / 8 := by
    rw [(hd x).fderiv, innerSL_apply_norm]
    exact affineFacetGradient_norm_le N a
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (hd z).differentiableAt)
    (fun z (_ : z ∈ Set.univ) => hb z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem affineFacet_weaklyConvex (N K m : ℕ) (a : FanFacet N) :
    WeaklyConvex 0 (affineFacet N K m a) := by
  simpa only [WeaklyConvex, zero_div, zero_mul, add_zero] using convexOn_affineFacet N K m a

def fanActiveGradients (N K m : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {v | ∃ a : FanFacet N, affineFacet N K m a x = euclideanTiltedBlock N K m x ∧
    v = affineFacetGradient N a}

def fanParameterizedBranch (N K m : ℕ) (a : FacetTuples 1 N) :
    EuclideanSpace ℝ (Fin N) → ℝ := affineFacet N K m (a 0)

theorem fanParameterizedBranch_joint_continuous (N K m : ℕ) :
    Continuous (fun p : FacetTuples 1 N × EuclideanSpace ℝ (Fin N) => fanParameterizedBranch N K m p.1 p.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro a
  exact continuous_affineFacet N K m (a 0)

theorem compactMaximum_fanParameterizedBranch (N K m : ℕ) :
    compactMaximum (fanParameterizedBranch N K m) = euclideanTiltedBlock N K m := by
  funext x
  have hg : IsGreatest (Set.range (fun a : FacetTuples 1 N => fanParameterizedBranch N K m a x))
      (euclideanTiltedBlock N K m x) := by
    constructor
    · obtain ⟨a, ha⟩ := affineFacet_attains_tiltedBlock N K m x
      exact ⟨fun _ => a, ha⟩
    · rintro _ ⟨a, rfl⟩
      exact affineFacet_le_tiltedBlock N K m (a 0) x
  exact hg.csSup_eq

theorem activeSlopes_fanParameterizedBranch (N K m : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    activeSlopes (fanParameterizedBranch N K m) x = fanActiveGradients N K m x := by
  ext v
  constructor
  · rintro ⟨a, ha, hv⟩
    change affineFacet N K m (a 0) x = compactMaximum (fanParameterizedBranch N K m) x at ha
    rw [compactMaximum_fanParameterizedBranch] at ha
    change v ∈ subdifferential (affineFacet N K m (a 0)) x at hv
    rw [subdifferential_affineFacet] at hv
    exact ⟨a 0, ha, hv⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun _ => a, ?_, ?_⟩
    · change affineFacet N K m a x = compactMaximum (fanParameterizedBranch N K m) x
      rwa [compactMaximum_fanParameterizedBranch]
    · change affineFacetGradient N a ∈ subdifferential (affineFacet N K m a) x
      rw [subdifferential_affineFacet]
      rfl

theorem subdifferential_euclideanTiltedBlock_eq_convexHull (N K m : ℕ)
    (x : EuclideanSpace ℝ (Fin N)) :
    subdifferential (euclideanTiltedBlock N K m) x = convexHull ℝ (fanActiveGradients N K m x) := by
  have h := subdifferential_compactMaximum_eq_convexHull
    (by positivity : (0 : ℝ) ≤ (N : ℝ) / 8) (by norm_num : (0 : ℝ) ≤ 0)
    (fanParameterizedBranch_joint_continuous N K m)
    (fun a : FacetTuples 1 N => affineFacet_lipschitz N K m (a 0))
    (fun a : FacetTuples 1 N => affineFacet_weaklyConvex N K m (a 0)) x
  rwa [compactMaximum_fanParameterizedBranch, activeSlopes_fanParameterizedBranch] at h

end WC
