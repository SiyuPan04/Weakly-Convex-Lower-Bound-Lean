import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Direct diagonal locality at zero activation

This file closes the only branch of condition (C2) not covered by the
positive-activation formula: a full subgradient at a point with
`activationNorm z = 0` has no coordinate beyond the next relay diagonal.

The proof is deliberately local.  On every forbidden coordinate we exhibit
both a positive and a negative one-block segment on which `hardValue` cannot
increase.  A sharp quadratic support inequality along arbitrarily short
initial pieces of those segments then forces the corresponding linear
coefficient to vanish.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- A quadratic support vector has nonpositive coordinate whenever the
function cannot increase on the positive coordinate segment. -/
theorem qSubgradient_coord_nonpos_of_positive_blockLine_le
    {M N : Nat} {c : ℝ} {z g : BlockVec M N}
    (hg : QSubgradient c (@hardValue M N) z g)
    (m : Fin M) (j : Fin N)
    (hle : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j 1) θ) ≤ hardValue z) :
    g m j ≤ 0 := by
  let v := shiftCoord (z m) j 1
  have hlinear : vecDot (g m) (v - z m) ≤ 0 := by
    apply linear_le_of_segment_quadratic
      (A := vecDot (g m) (v - z m)) (B := 0)
      (C := c * vecSq (v - z m))
    intro θ hθ hθ1
    have hq := hg (blockLine z m v θ)
    rw [blockDot_blockLine_sub, blockSq_blockLine_sub] at hq
    have hf : hardValue (blockLine z m v θ) ≤ hardValue z := by
      simpa [v] using hle θ hθ.le hθ1
    nlinarith
  dsimp [v] at hlinear
  rw [vecDot_shiftCoord_sub] at hlinear
  simpa using hlinear

/-- The analogous sign conclusion from a nonincreasing negative segment. -/
theorem qSubgradient_coord_nonneg_of_negative_blockLine_le
    {M N : Nat} {c r : ℝ} {z g : BlockVec M N}
    (hg : QSubgradient c (@hardValue M N) z g)
    (m : Fin M) (j : Fin N) (hr : r < 0)
    (hle : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j r) θ) ≤ hardValue z) :
    0 ≤ g m j := by
  let v := shiftCoord (z m) j r
  have hlinear : vecDot (g m) (v - z m) ≤ 0 := by
    apply linear_le_of_segment_quadratic
      (A := vecDot (g m) (v - z m)) (B := 0)
      (C := c * vecSq (v - z m))
    intro θ hθ hθ1
    have hq := hg (blockLine z m v θ)
    rw [blockDot_blockLine_sub, blockSq_blockLine_sub] at hq
    have hf : hardValue (blockLine z m v θ) ≤ hardValue z := by
      simpa [v] using hle θ hθ.le hθ1
    nlinarith
  dsimp [v] at hlinear
  rw [vecDot_shiftCoord_sub] at hlinear
  nlinarith

/-- At a zero coordinate, increasing that coordinate cannot increase the
hard value: the tilted fan decreases while the progress carrier increases.
-/
theorem positive_zero_coordinate_hardValue_blockLine_le
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (m : Fin M) (j : Fin N) (hzj : z m j = 0) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j 1) θ) ≤ hardValue z := by
  intro θ hθ _hθ1
  apply hardValue_blockLine_le_of_phi_le hA.M_pos hA.N_pos
  · rw [blockLine_shiftCoord_same]
    exact phi_shiftCoord_le hA.N_pos (z m) j (mul_nonneg hθ (by norm_num))
  · rw [blockLine_shiftCoord_same]
    exact psi_le_shiftCoord_of_coord_eq_zero hA.N_pos
      (z m) j (θ * 1) hzj

/-- If a positive-index coordinate is beyond the next diagonal, its tilted
facet is inactive.  A sufficiently short negative shift therefore leaves
the fan unchanged and cannot increase the hard value. -/
theorem exists_negative_positive_index_hardValue_blockLine_le
    {M N t : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (hz : Reachable (relayDelay N) t z) (m : Fin M) (j : Fin N)
    (hj : 0 < j.1)
    (hlevel : t + 1 ≤ level (relayDelay N) m.1 j.1) :
    ∃ r : ℝ, r < 0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j r) θ) ≤ hardValue z := by
  let k := j.1 - 1
  have hkN : k < N := by
    dsimp [k]
    omega
  have hzprefix : PrefixSupported k (z m) := by
    intro i hi
    apply hz m i
    unfold level at hlevel ⊢
    dsimp [k] at hi
    omega
  have hinactive : ¬ ActiveFacet (z m) (some j) := by
    intro hactive
    have hindex := activeFacet_index_le_first_hidden
      hA.N_pos hkN hzprefix hactive
    dsimp [k] at hindex
    omega
  obtain ⟨r, hr, hphi⟩ :=
    exists_negative_phi_shift_segment_eq_of_inactive
      hA.N_pos (z m) j hinactive
  refine ⟨r, hr, ?_⟩
  intro θ hθ hθ1
  have hzj : z m j = 0 := hz m j (by omega)
  apply hardValue_blockLine_le_of_phi_le hA.M_pos hA.N_pos
  · rw [blockLine_shiftCoord_same]
    exact (hphi θ hθ hθ1).le
  · rw [blockLine_shiftCoord_same]
    exact psi_le_shiftCoord_of_coord_eq_zero hA.N_pos
      (z m) j (θ * r) hzj

/-- In fact the segment argument is stronger than the zero-activation case:
it proves the required one-diagonal advance at every reachable point, without
selecting or reconstructing an outer maximizer. -/
theorem fullSubdiff_one_reachable_locality
    {M N t : Nat} (hA : Admissible M N) {z g : BlockVec M N}
    (hz : Reachable (relayDelay N) t z)
    (hg : g ∈ fullSubdiff 1 (@hardValue M N) z) :
    Reachable (relayDelay N) (t + 1) g := by
  intro m j hlevel
  have hzj : z m j = 0 := hz m j (by omega)
  have hgsharp := fullSubdiff_one_subset_threeQuarter hA z hg
  rw [mem_fullSubdiff_iff_qSubgradient] at hgsharp
  norm_num at hgsharp
  apply le_antisymm
  · exact qSubgradient_coord_nonpos_of_positive_blockLine_le
      hgsharp m j
      (positive_zero_coordinate_hardValue_blockLine_le hA m j hzj)
  · by_cases hj : j.1 = 0
    · obtain ⟨r, hr, hline⟩ :=
        exists_negative_zero_index_hardValue_blockLine_le
          hA hz m j hj hlevel
      exact qSubgradient_coord_nonneg_of_negative_blockLine_le
        hgsharp m j hr hline
    · obtain ⟨r, hr, hline⟩ :=
        exists_negative_positive_index_hardValue_blockLine_le
          hA hz m j (Nat.pos_of_ne_zero hj) hlevel
      exact qSubgradient_coord_nonneg_of_negative_blockLine_le
        hgsharp m j hr hline

/-- The requested zero-activation branch of C2. -/
theorem fullSubdiff_one_zero_activation_locality
    {M N t : Nat} (hA : Admissible M N) {z g : BlockVec M N}
    (hz : Reachable (relayDelay N) t z)
    (_hR0 : activationNorm z = 0)
    (hg : g ∈ fullSubdiff 1 (@hardValue M N) z) :
    Reachable (relayDelay N) (t + 1) g :=
  fullSubdiff_one_reachable_locality hA hz hg

/-- Unconditional semantic condition (C2) for the standard full
subdifferential of the normalized hard instance. -/
theorem hardValue_fullSubdiff_diagonal_locality {M N : Nat}
    (hA : Admissible M N) :
    HasDiagonalLocality (relayDelay N)
      (fullSubdiff 1 (@hardValue M N)) := by
  intro t z hz g hg
  exact fullSubdiff_one_reachable_locality hA hz hg

end

end WeaklyConvexLowerBound

