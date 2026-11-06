import WC.SourceGrouping
import WC.TerminalDistance
import WC.RadialInnerBound
import WC.Isometry
import WC.ChainBandBudget

/-! Pointwise barriers at a nearby proximal point, after an arbitrary
orthonormal embedding. All subgradients are the actual Fréchet ones. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem lifted_chain_radial_inner_lower {M N : ℕ} (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (p h : E)
    (hh : h ∈ subdifferential (isometricLift U chainMajorant) p) :
    -chainRadialConstant M N ≤ inner ℝ h p := by
  rw [subdifferential, frechetSubdifferential_isometricLift p U (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (chainMajorant_weaklyConvex (by omega))] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  have hi := U.toContinuousLinearMap.adjoint_inner_right g p
  change inner ℝ g (isometryProjection U p) = inner ℝ (U g) p at hi
  rw [← hi]
  exact chainMajorant_radial_inner_lower hN hg

theorem terminal_distance_lower_of_small_coordinates {M N : ℕ} (hN : 0 < N)
    (x q : ChainSpace M N) (hq : q ∈ terminalRegion)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, x i ≤ 1 / (N : ℝ)) :
    5 / Real.sqrt (N : ℝ) ≤ ‖x - q‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hd := norm_sub_terminalRegion_lower hN
    (show 1 / (N : ℝ) ≤ 6 / (N : ℝ) by apply div_le_div_of_nonneg_right (by norm_num) hNR.le)
    x q hq s hcard hsmall
  have hid : (6 / (N : ℝ) - 1 / (N : ℝ)) * Real.sqrt (N : ℝ) =
      5 / Real.sqrt (N : ℝ) := by
    apply (eq_div_iff hs.ne').mpr
    rw [mul_assoc, Real.mul_self_sqrt hNR.le]
    field_simp
    norm_num
  rwa [hid] at hd

theorem lifted_chain_subgradient_norm_sq_lower {M N B : ℕ} (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x p h : E)
    (hcoverage : chainSourceRadius M N ≤ (8 : ℝ) ^ B * chainNearRadius N)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, isometryProjection U x i ≤ 1 / (N : ℝ))
    (hdist : ‖x - p‖ ≤ 1 / Real.sqrt (N : ℝ))
    (hh : h ∈ subdifferential (isometricLift U chainMajorant) p) :
    1 / (25 * (N : ℝ) + 8 * (B : ℝ)) ≤ ‖h‖ ^ 2 := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hfar : ∀ q ∈ terminalRegion, chainNearRadius N < ‖isometryProjection U p - q‖ := by
    intro q hq
    have hlower := terminal_distance_lower_of_small_coordinates hNpos
      (isometryProjection U x) q hq s hcard hsmall
    have htriangle := norm_add_le (isometryProjection U x - isometryProjection U p)
      (isometryProjection U p - q)
    rw [sub_add_sub_cancel] at htriangle
    have hcontract := isometryProjection_norm_le U (x - p)
    rw [map_sub] at hcontract
    have hr : chainNearRadius N < 4 / Real.sqrt (N : ℝ) := by
      unfold chainNearRadius
      apply (div_lt_div_iff₀ (mul_pos (by norm_num) hs) hs).mpr
      nlinarith
    have heq : 5 / Real.sqrt (N : ℝ) = 4 / Real.sqrt (N : ℝ) + 1 / Real.sqrt (N : ℝ) := by ring
    linarith
  rw [subdifferential, frechetSubdifferential_isometricLift p U (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (chainMajorant_weaklyConvex hNpos)] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  rw [U.norm_map]
  exact chainMajorant_subgradient_norm_sq_lower hN _ hcoverage hfar hg

end WC
