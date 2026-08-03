import WeaklyConvexLowerBound.ZeroActivationFullFormula

/-!
# Audited finite-max upper model for the zero-activation formula

This file records a reusable fact found while auditing the missing reverse
inclusion at zero activation.  A finite max-affine function admits a
first-order upper model whose slope is the largest slope among the active
facets.  Crucially, no local active-set stability or limiting argument is
needed: the strict gap of every inactive facet absorbs its linear excess
into an explicit quadratic remainder.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The elementary completion-of-the-square estimate which absorbs the
linear excess of an inactive affine facet into its strict value gap. -/
theorem inactiveGap_absorbs_linear_excess
    {gap A B t : ℝ} (hgap : 0 < gap) :
    -gap + t * A ≤
      t * B + ((A - B) ^ 2 / (4 * gap)) * t ^ 2 := by
  have hden : 0 < 4 * gap := by positivity
  have heq :
      (t * B + ((A - B) ^ 2 / (4 * gap)) * t ^ 2) -
          (-gap + t * A) =
        (2 * gap - t * (A - B)) ^ 2 / (4 * gap) := by
    field_simp [hgap.ne']
    ring
  have hnonneg : 0 ≤
      (t * B + ((A - B) ^ 2 / (4 * gap)) * t ^ 2) -
        (-gap + t * A) := by
    rw [heq]
    exact div_nonneg (sq_nonneg _) hden.le
  linarith

/-- Quadratic price assigned to one inactive facet.  Active facets need no
remainder because their directional slope is bounded separately. -/
noncomputable def facetGapRemainder {N : Nat} (u d : Fin N → ℝ) (B : ℝ)
    (s : FacetIndex N) : ℝ :=
  by
    classical
    exact if ActiveFacet u s then 0
      else (vecDot (facetSlope s) d - B) ^ 2 /
        (4 * (phi u - facetValue u s))

/-- Sum of the finitely many inactive-facet prices.  A sum is used instead
of a maximum so that every individual nonnegative price is immediately
bounded by the total. -/
def phiGapRemainder {N : Nat} (u d : Fin N → ℝ) (B : ℝ) : ℝ :=
  ∑ s : FacetIndex N, facetGapRemainder u d B s

theorem facetGapRemainder_nonneg {N : Nat} (u d : Fin N → ℝ)
    (B : ℝ) (s : FacetIndex N) :
    0 ≤ facetGapRemainder u d B s := by
  classical
  by_cases hs : ActiveFacet u s
  · rw [facetGapRemainder, if_pos hs]
  · rw [facetGapRemainder, if_neg hs]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (facetValue_le_phi u s)))

theorem phiGapRemainder_nonneg {N : Nat} (u d : Fin N → ℝ) (B : ℝ) :
    0 ≤ phiGapRemainder u d B := by
  unfold phiGapRemainder
  exact Finset.sum_nonneg fun s _ ↦ facetGapRemainder_nonneg u d B s

theorem facetGapRemainder_le_phiGapRemainder {N : Nat}
    (u d : Fin N → ℝ) (B : ℝ) (s : FacetIndex N) :
    facetGapRemainder u d B s ≤ phiGapRemainder u d B := by
  unfold phiGapRemainder
  exact Finset.single_le_sum
    (fun r _ ↦ facetGapRemainder_nonneg u d B r)
    (Finset.mem_univ s)

/-- Every individual facet lies below the audited quadratic model. -/
theorem facetValue_line_le_activeSlope_add_quadratic {N : Nat}
    (u d : Fin N → ℝ) (B t : ℝ) (ht : 0 ≤ t)
    (hactive : ∀ s : FacetIndex N,
      ActiveFacet u s → vecDot (facetSlope s) d ≤ B)
    (s : FacetIndex N) :
    facetValue (u + t • d) s ≤
      phi u + t * B + phiGapRemainder u d B * t ^ 2 := by
  classical
  have hline : facetValue (u + t • d) s =
      facetValue u s + t * vecDot (facetSlope s) d := by
    rw [facetValue_affine u (u + t • d) s]
    have hsub : u + t • d - u = t • d := by
      ext i
      simp
    rw [hsub, vecDot_smul_right_param]
  rw [hline]
  by_cases hs : ActiveFacet u s
  · have hsval : facetValue u s = phi u := hs
    rw [hsval]
    have hslope := hactive s hs
    have hmul := mul_le_mul_of_nonneg_left hslope ht
    have hrem := mul_nonneg (phiGapRemainder_nonneg u d B) (sq_nonneg t)
    linarith
  · have hgap : 0 < phi u - facetValue u s := by
      have hne : facetValue u s ≠ phi u := hs
      exact sub_pos.mpr (lt_of_le_of_ne (facetValue_le_phi u s) hne)
    have habsorb := inactiveGap_absorbs_linear_excess
      (gap := phi u - facetValue u s)
      (A := vecDot (facetSlope s) d) (B := B) (t := t) hgap
    have hfacet : facetGapRemainder u d B s =
        (vecDot (facetSlope s) d - B) ^ 2 /
          (4 * (phi u - facetValue u s)) := by
      simp only [facetGapRemainder, if_neg hs]
    have hprice := facetGapRemainder_le_phiGapRemainder u d B s
    rw [hfacet] at hprice
    have hpriceMul := mul_le_mul_of_nonneg_right hprice (sq_nonneg t)
    linarith

/-- Finite-max quadratic upper model.  This is the short replacement for
the usual "the active set is locally constant" argument.

`B` only has to dominate slopes of facets active at the base point.  The
explicit finite remainder handles every inactive facet automatically. -/
theorem phi_line_le_activeSlope_add_quadratic {N : Nat}
    (u d : Fin N → ℝ) (B t : ℝ) (ht : 0 ≤ t)
    (hactive : ∀ s : FacetIndex N,
      ActiveFacet u s → vecDot (facetSlope s) d ≤ B) :
    phi (u + t • d) ≤
      phi u + t * B + phiGapRemainder u d B * t ^ 2 := by
  change (Finset.univ : Finset (FacetIndex N)).sup'
      Finset.univ_nonempty (facetValue (u + t • d)) ≤
    phi u + t * B + phiGapRemainder u d B * t ^ 2
  apply Finset.sup'_le Finset.univ_nonempty
  intro s _
  exact facetValue_line_le_activeSlope_add_quadratic
    u d B t ht hactive s

/-! ## The matching upper model for the outer positive-part norm -/

/-- At a nonpositive base vector, only the exactly-zero coordinates survive
to first order. -/
noncomputable def zeroScoreLinearPart {M : Nat}
    (s a : Fin M → ℝ) : Fin M → ℝ := by
  classical
  exact fun m ↦ if s m = 0 then a m else 0

/-- A negative base coordinate has a strict gap `-s m`; its possible
first-order leakage is priced by the same completion-of-the-square term as
an inactive affine facet. -/
noncomputable def zeroScoreQuadraticPart {M : Nat}
    (s a c : Fin M → ℝ) : Fin M → ℝ := by
  classical
  exact fun m ↦ c m + if s m = 0 then 0 else (a m) ^ 2 / (4 * (-s m))

theorem zeroScore_coordinate_upper {M : Nat}
    {s a c y : Fin M → ℝ} (hs : ∀ m, s m ≤ 0)
    {t : ℝ}
    (hy : ∀ m, y m ≤ s m + t * a m + c m * t ^ 2)
    (m : Fin M) :
    y m ≤
      t * zeroScoreLinearPart s a m +
        zeroScoreQuadraticPart s a c m * t ^ 2 := by
  classical
  by_cases hsm : s m = 0
  · simp only [zeroScoreLinearPart, zeroScoreQuadraticPart, if_pos hsm]
    have hym := hy m
    rw [hsm, zero_add] at hym
    simpa using hym
  · have hsneg : s m < 0 := lt_of_le_of_ne (hs m) hsm
    have hgap : 0 < -s m := neg_pos.mpr hsneg
    have habsorb := inactiveGap_absorbs_linear_excess
      (gap := -s m) (A := a m) (B := 0) (t := t) hgap
    simp only [zeroScoreLinearPart, zeroScoreQuadraticPart, if_neg hsm,
      mul_zero, zero_add]
    have hym := hy m
    simp only [neg_neg, mul_zero, sub_zero, zero_add] at habsorb
    calc
      y m ≤ s m + t * a m + c m * t ^ 2 := hym
      _ ≤ (a m) ^ 2 / (4 * (-s m)) * t ^ 2 + c m * t ^ 2 := by
        linarith
      _ = (c m + (a m) ^ 2 / (4 * (-s m))) * t ^ 2 := by ring

/-- Quadratic upper model for `positiveNorm` at an arbitrary nonpositive
base vector.  This is the outer analogue of
`phi_line_le_activeSlope_add_quadratic`.

The proof uses the variational representation with the canonical weight at
`y`; hence it avoids square-root estimates and remains valid even when
`positiveNorm y = 0`. -/
theorem positiveNorm_zeroBase_quadratic_upper {M : Nat}
    {s a c y : Fin M → ℝ} (hs : ∀ m, s m ≤ 0)
    {t : ℝ} (ht : 0 ≤ t)
    (hy : ∀ m, y m ≤ s m + t * a m + c m * t ^ 2) :
    positiveNorm y ≤
      t * positiveNorm (zeroScoreLinearPart s a) +
        t ^ 2 * positiveNorm (zeroScoreQuadraticPart s a c) := by
  let w : Fin M → ℝ := canonicalOuterWeight y
  have hw : FeasibleOuterWeight w := canonicalOuterWeight_feasible y
  have hcoord (m : Fin M) :
      y m ≤ t * zeroScoreLinearPart s a m +
        zeroScoreQuadraticPart s a c m * t ^ 2 :=
    zeroScore_coordinate_upper hs hy m
  have hdot : outerDot w y ≤
      t * outerDot w (zeroScoreLinearPart s a) +
        t ^ 2 * outerDot w (zeroScoreQuadraticPart s a c) := by
    unfold outerDot
    calc
      (∑ m, w m * y m) ≤
          ∑ m, w m *
            (t * zeroScoreLinearPart s a m +
              zeroScoreQuadraticPart s a c m * t ^ 2) := by
        apply Finset.sum_le_sum
        intro m _
        exact mul_le_mul_of_nonneg_left (hcoord m) (hw.1 m)
      _ = t * (∑ m, w m * zeroScoreLinearPart s a m) +
          t ^ 2 * (∑ m, w m * zeroScoreQuadraticPart s a c m) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m _
        ring
  have hlinear := outerDot_le_positiveNorm
    (s := zeroScoreLinearPart s a) hw
  have hquadratic := outerDot_le_positiveNorm
    (s := zeroScoreQuadraticPart s a c) hw
  have hlinearScaled := mul_le_mul_of_nonneg_left hlinear ht
  have hquadraticScaled :=
    mul_le_mul_of_nonneg_left hquadratic (sq_nonneg t)
  rw [canonicalOuterWeight_dot] at hdot
  exact hdot.trans (add_le_add hlinearScaled hquadraticScaled)

/-- The canonical weight of the first-order zero-score vector pairs to zero
with the original base vector.  No sign assumption is needed for this
identity: coordinates not equal to zero are erased before normalization. -/
theorem outerDot_canonical_zeroScoreLinearPart_base_eq_zero {M : Nat}
    (s a : Fin M → ℝ) :
    outerDot (canonicalOuterWeight (zeroScoreLinearPart s a)) s = 0 := by
  classical
  unfold outerDot
  apply Finset.sum_eq_zero
  intro m _
  by_cases hsm : s m = 0
  · rw [hsm, mul_zero]
  · simp [canonicalOuterWeight, zeroScoreLinearPart, hsm]

/-- At a zero-activation hard point, normalizing any candidate first-order
score vector after erasing negative-score coordinates gives a literal active
outer weight at the base point. -/
theorem canonical_zeroScoreLinearPart_activeOuterWeight {M N : Nat}
    {z : BlockVec M N} (hR0 : activationNorm z = 0)
    (a : Fin M → ℝ) :
    ActiveOuterWeight z
      (canonicalOuterWeight (zeroScoreLinearPart (sigmaScore z) a)) := by
  constructor
  · exact canonicalOuterWeight_feasible _
  · rw [outerDot_canonical_zeroScoreLinearPart_base_eq_zero, hR0]

/-! ## A best active tilted facet in each direction -/

/-- The finite active-facet set contains a facet whose slope realizes the
largest pairing with a prescribed direction. -/
theorem exists_activeFacet_slope_max {N : Nat}
    (u d : Fin N → ℝ) :
    ∃ s : FacetIndex N, ActiveFacet u s ∧
      ∀ r : FacetIndex N, ActiveFacet u r →
        vecDot (facetSlope r) d ≤ vecDot (facetSlope s) d := by
  classical
  let active : Finset (FacetIndex N) :=
    Finset.univ.filter (ActiveFacet u)
  have hactive : active.Nonempty := by
    obtain ⟨s, hs⟩ := exists_activeFacet u
    exact ⟨s, by simp [active, hs]⟩
  obtain ⟨s, hs, hsmax⟩ :=
    Finset.exists_mem_eq_sup' hactive
      (fun r : FacetIndex N ↦ vecDot (facetSlope r) d)
  refine ⟨s, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hs).2
  · intro r hr
    have hrmem : r ∈ active := by simp [active, hr]
    have hrle := Finset.le_sup'
      (fun q : FacetIndex N ↦ vecDot (facetSlope q) d) hrmem
    simpa [hsmax] using hrle

/-! ## Exact compact maximum API used by the separation route -/

/-- The displayed zero-activation formula set realizes the maximum of its
pairing with every block direction.  This packages the exact Mathlib
extreme-value API needed if the final proof chooses a fixed support
maximizer rather than a `t`-dependent displayed reply. -/
theorem hardFormulaSet_exists_blockDot_max {M N : Nat}
    (hN : 0 < N) {z : BlockVec M N} (hR0 : activationNorm z = 0)
    (d : BlockVec M N) :
    ∃ q ∈ hardFormulaSet z,
      ∀ r ∈ hardFormulaSet z, blockDot r d ≤ blockDot q d := by
  have hcontinuous : Continuous (fun q : BlockVec M N ↦ blockDot q d) := by
    unfold blockDot
    fun_prop
  obtain ⟨q, hq, hqmax⟩ :=
    (hardFormulaSet_isCompact hN z).exists_isMaxOn
      (hardFormulaSet_nonempty_of_activationNorm_eq_zero hR0)
      hcontinuous.continuousOn
  exact ⟨q, hq, hqmax⟩

/-- Independent case-split audit of the all-point exact
full-subdifferential characterization. -/
theorem fullSubdiff_eq_convexHull_hardFormulaSet_via_case_split_audit
    {M N : Nat} (hA : Admissible M N) (z : BlockVec M N) :
    fullSubdiff 1 (@hardValue M N) z =
      convexHull ℝ (hardFormulaSet z) := by
  by_cases hR : 0 < activationNorm z
  · exact fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_pos hA hR
  · have hR0 : activationNorm z = 0 :=
      le_antisymm (le_of_not_gt hR) (by
        unfold activationNorm
        exact Real.sqrt_nonneg _)
    exact fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_eq_zero
      hA hR0

end

end WeaklyConvexLowerBound

