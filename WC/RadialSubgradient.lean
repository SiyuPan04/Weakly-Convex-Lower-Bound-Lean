import WC.BinaryMaximumRule
import WC.RadialExterior

/-! Exact active-branch calculus and a unified subgradient mixture for the radial wall. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [ProperSpace E] [FiniteDimensional ℝ E] in
theorem radialBranch_subdifferential {f : E → ℝ} {R : ℝ} {x : E} (hx : x ≠ 0) :
    subdifferential (radialBranch f R) x = {(3 / ‖x‖) • x} := by
  ext v
  exact frechetSubgradient_iff_gradient (radialBranch_hasGradientAt hx)

theorem radialWall_subdifferential_chain {f : E → ℝ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hLip : GloballyLipschitz 2 f) (hWC : WeaklyConvex ρ f)
    {x : E} (hx : radialBranch f R x < f x) :
    subdifferential (radialWall f R) x = subdifferential f x :=
  subdifferential_max_left_of_lt (by norm_num : (0 : ℝ) ≤ 3) hρ (hLip.mono (by norm_num))
    (radialBranch_lipschitz f R) hWC (radialBranch_weaklyConvex hρ f R) hx

theorem radialWall_subdifferential_wall {f : E → ℝ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 < R) (hLip : GloballyLipschitz 2 f) (hWC : WeaklyConvex ρ f)
    {x : E} (hx : f x < radialBranch f R x) :
    subdifferential (radialWall f R) x = {(3 / ‖x‖) • x} := by
  have hxne : x ≠ 0 := by
    intro heq
    subst x
    simp only [radialBranch, norm_zero] at hx
    linarith
  exact (subdifferential_max_right_of_lt (by norm_num : (0 : ℝ) ≤ 3) hρ (hLip.mono (by norm_num))
    (radialBranch_lipschitz f R) hWC (radialBranch_weaklyConvex hρ f R) hx).trans
    (radialBranch_subdifferential hxne)

theorem radialWall_subdifferential_tie {f : E → ℝ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 < R) (hLip : GloballyLipschitz 2 f) (hWC : WeaklyConvex ρ f)
    {x : E} (hx : f x = radialBranch f R x) :
    subdifferential (radialWall f R) x = convexHull ℝ (subdifferential f x ∪ {(3 / ‖x‖) • x}) := by
  have hxne : x ≠ 0 := by
    intro heq
    subst x
    simp only [radialBranch, norm_zero] at hx
    linarith
  rw [show subdifferential (radialWall f R) x =
      convexHull ℝ (subdifferential f x ∪ subdifferential (radialBranch f R) x) from
    subdifferential_max_of_eq (by norm_num : (0 : ℝ) ≤ 3) hρ (hLip.mono (by norm_num))
      (radialBranch_lipschitz f R) hWC (radialBranch_weaklyConvex hρ f R) hx]
  rw [radialBranch_subdifferential hxne]

/-- All actual wall subgradients either lie in the chain subdifferential, or admit
the radial mixture used in the noncancellation argument. -/
theorem radialWall_subgradient_cases {f : E → ℝ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 < R) (hLip : GloballyLipschitz 2 f) (hWC : WeaklyConvex ρ f)
    {x v : E} (hv : v ∈ subdifferential (radialWall f R) x) :
    v ∈ subdifferential f x ∨ ∃ (w : ℝ) (h : E), 0 ≤ w ∧ w ≤ 1 ∧ h ∈ subdifferential f x ∧
      f x ≤ radialBranch f R x ∧ x ≠ 0 ∧
      v = w • h + (3 * (1 - w)) • (‖x‖⁻¹ • x) := by
  by_cases hchain : radialBranch f R x < f x
  · exact Or.inl ((radialWall_subdifferential_chain hρ hLip hWC hchain) ▸ hv)
  have hactive : f x ≤ radialBranch f R x := le_of_not_gt hchain
  have hxne : x ≠ 0 := by
    intro heq
    subst x
    simp only [radialBranch, norm_zero] at hactive
    linarith
  have hvactive : v ∈ convexHull ℝ (binaryActiveSlopes f (radialBranch f R) x) := by
    change v ∈ subdifferential (fun y => max (f y) (radialBranch f R y)) x at hv
    rwa [subdifferential_max_eq_convexHull (by norm_num : (0 : ℝ) ≤ 3) hρ
      (hLip.mono (by norm_num)) (radialBranch_lipschitz f R) hWC (radialBranch_weaklyConvex hρ f R)] at hv
  have hsub : binaryActiveSlopes f (radialBranch f R) x ⊆ subdifferential f x ∪ {(3 / ‖x‖) • x} := by
    intro g hg
    rcases hg with ⟨_, hg⟩ | ⟨_, hg⟩
    · exact Or.inl hg
    · exact Or.inr ((radialBranch_subdifferential hxne) ▸ hg)
  have hvunion := convexHull_mono hsub hvactive
  obtain ⟨w, h, hw0, hw1, hh, hrep⟩ := convexHull_union_singleton_representation
    (subdifferential_convex x hρ hWC) (subdifferential_nonempty x (by norm_num : (0 : ℝ) ≤ 2) hρ hLip hWC)
    ((3 / ‖x‖) • x) hvunion
  have hid : (1 - w) • ((3 / ‖x‖) • x) = (3 * (1 - w)) • (‖x‖⁻¹ • x) := by
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hid] at hrep
  exact Or.inr ⟨w, h, hw0, hw1, hh, hactive, hxne, hrep⟩

omit [InnerProductSpace ℝ E] [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem radialBranch_active_norm_lower {f : E → ℝ} {Δ R : ℝ} (hgap : GapBound Δ f)
    {x : E} (hactive : f x ≤ radialBranch f R x) : R - Δ / 3 ≤ ‖x‖ := by
  have h := hgap x
  unfold radialBranch at hactive
  linarith

theorem radialWall_subdifferential_zero {f : E → ℝ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 < R) (hLip : GloballyLipschitz 2 f) (hWC : WeaklyConvex ρ f) :
    subdifferential (radialWall f R) 0 = subdifferential f 0 := by
  apply radialWall_subdifferential_chain hρ hLip hWC
  simp only [radialBranch, norm_zero]
  linarith

end WC
