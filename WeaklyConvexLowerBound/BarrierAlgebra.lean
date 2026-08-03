import WeaklyConvexLowerBound.Basic
import WeaklyConvexLowerBound.CoreFunctions

/-!
# Algebraic stationarity barrier

This file isolates the finite-sum argument in TeX lines 1945--1983.  It does
not use differentiability: the only input from the tilted max-affine block is
the explicit `PhiSubgradient` representation from `CoreFunctions`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

private theorem weightedFacetSlope_coord {N : Nat}
    (weights : FacetIndex N → ℝ) (i : Fin N) :
    (∑ s, weights s * facetSlope s i) =
      -(N : ℝ) / 8 * weights (some i) := by
  classical
  rw [Finset.sum_eq_single (some i)]
  · rw [facetSlope_some_same]
    ring
  · intro s _ hsi
    cases s with
    | none => simp
    | some j =>
        have hij : i ≠ j := by
          intro hij
          apply hsi
          simp [hij]
        simp [facetSlope, hij]
  · simp

private theorem sum_option_weights {N : Nat} (weights : FacetIndex N → ℝ) :
    (∑ s, weights s) = weights none + ∑ j : Fin N, weights (some j) := by
  classical
  rw [show (Finset.univ : Finset (FacetIndex N)) =
      Finset.insertNone (Finset.univ : Finset (Fin N)) by
    ext s
    cases s <;> simp]
  simpa using
    (Finset.sum_insertNone weights (Finset.univ : Finset (Fin N)))

/-- Every coordinate of a tilted-block subgradient is nonpositive. -/
theorem phiSubgradient_coord_nonpos {N : Nat} {x u : Fin N → ℝ}
    (hu : PhiSubgradient x u) (i : Fin N) : u i ≤ 0 := by
  obtain ⟨weights, hweights_nonneg, _hweights_sum,
    _hweights_active, hucoord⟩ := hu
  rw [hucoord i, weightedFacetSlope_coord]
  have hw := hweights_nonneg (some i)
  have hnegN8 : -(N : ℝ) / 8 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg N)) (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg hnegN8 hw

/-- Positivity of `phi` rules out its constant zero branch. -/
theorem none_not_active_of_phi_pos {N : Nat} {x : Fin N → ℝ}
    (hphi : 0 < phi x) : ¬ActiveFacet x (none : FacetIndex N) := by
  intro hactive
  change facetValue x none = phi x at hactive
  simp only [facetValue_none] at hactive
  linarith

/-- If the zero branch is inactive, the negative coordinates of a block
subgradient have total mass exactly `N/8`. -/
theorem phiSubgradient_neg_sum_eq {N : Nat} {x u : Fin N → ℝ}
    (hu : PhiSubgradient x u)
    (hzero : ¬ActiveFacet x (none : FacetIndex N)) :
    (∑ i, -u i) = (N : ℝ) / 8 := by
  obtain ⟨weights, _hweights_nonneg, hweights_sum,
    hweights_active, hucoord⟩ := hu
  have hweight_none : weights none = 0 := by
    by_contra hne
    exact hzero (hweights_active none hne)
  have hweights_some : (∑ i : Fin N, weights (some i)) = 1 := by
    have hsplit := sum_option_weights weights
    rw [hsplit, hweight_none, zero_add] at hweights_sum
    exact hweights_sum
  have hucoord' (i : Fin N) :
      u i = -(N : ℝ) / 8 * weights (some i) := by
    rw [hucoord i, weightedFacetSlope_coord]
  calc
    (∑ i, -u i) =
        ∑ i : Fin N, (N : ℝ) / 8 * weights (some i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hucoord' i]
      ring
    _ = (N : ℝ) / 8 * ∑ i : Fin N, weights (some i) := by
      rw [Finset.mul_sum]
    _ = (N : ℝ) / 8 := by rw [hweights_some, mul_one]

theorem phiSubgradient_neg_sum_eq_of_phi_pos {N : Nat}
    {x u : Fin N → ℝ} (hu : PhiSubgradient x u) (hphi : 0 < phi x) :
    (∑ i, -u i) = (N : ℝ) / 8 :=
  phiSubgradient_neg_sum_eq hu (none_not_active_of_phi_pos hphi)

/-- Finite Cauchy--Schwarz converts the exact `ℓ₁` mass into the squared
Euclidean lower bound used by the barrier argument. -/
theorem phiSubgradient_energy {N : Nat} {x u : Fin N → ℝ}
    (hu : PhiSubgradient x u)
    (hzero : ¬ActiveFacet x (none : FacetIndex N)) :
    ((N : ℝ) / 8) ^ 2 ≤ (N : ℝ) * ∑ i, (u i) ^ 2 := by
  have hmass := phiSubgradient_neg_sum_eq hu hzero
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => -u i)
  have hcs' :
      (∑ i, -u i) ^ 2 ≤ (N : ℝ) * ∑ i, (u i) ^ 2 := by
    simpa [sq] using hcs
  rw [hmass] at hcs'
  exact hcs'

theorem phiSubgradient_energy_of_phi_pos {N : Nat}
    {x u : Fin N → ℝ} (hu : PhiSubgradient x u) (hphi : 0 < phi x) :
    ((N : ℝ) / 8) ^ 2 ≤ (N : ℝ) * ∑ i, (u i) ^ 2 :=
  phiSubgradient_energy hu (none_not_active_of_phi_pos hphi)

/-! ## Assembly over all blocks -/

/-- All purely algebraic data needed for the final barrier.  In accordance
with the TeX proof, the zero branch is required to be inactive only in blocks
whose weight is nonzero.  The final lower bound is deliberately not a field.
-/
structure BarrierAlgebraData (M N : Nat) where
  point : BlockVec M N
  u : BlockVec M N
  weights : Fin M → ℝ
  a : Fin M → ℝ
  progressGrad : BlockVec M N
  g : BlockVec M N
  u_subgradient : ∀ m, PhiSubgradient (point m) (u m)
  zero_inactive : ∀ m, weights m ≠ 0 →
    ¬ActiveFacet (point m) (none : FacetIndex N)
  weights_nonneg : ∀ m, 0 ≤ weights m
  weights_sq_sum : (∑ m, (weights m) ^ 2) = 1
  a_nonneg : ∀ m, 0 ≤ a m
  progressGrad_nonneg : ∀ m j, 0 ≤ progressGrad m j
  g_eq : ∀ m j, g m j =
    (2 / (N : ℝ)) * (weights m * u m j - a m * progressGrad m j)

private theorem barrier_block_lower {M N : Nat} (hN : 0 < N)
    (d : BarrierAlgebraData M N) (m : Fin M) :
    (d.weights m) ^ 2 / (16 * (N : ℝ)) ≤ ∑ j, (d.g m j) ^ 2 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  by_cases hw : d.weights m = 0
  · rw [hw]
    norm_num
    exact Finset.sum_nonneg fun j _ => sq_nonneg (d.g m j)
  · have henergy := phiSubgradient_energy (d.u_subgradient m)
      (d.zero_inactive m hw)
    have hU : (N : ℝ) / 64 ≤ ∑ j, (d.u m j) ^ 2 := by
      have hdiv : ((N : ℝ) / 8) ^ 2 / (N : ℝ) ≤
          ∑ j, (d.u m j) ^ 2 := by
        apply (div_le_iff₀ hNR).2
        simpa [mul_comm] using henergy
      have hid : ((N : ℝ) / 8) ^ 2 / (N : ℝ) = (N : ℝ) / 64 := by
        field_simp [ne_of_gt hNR]
        ring
      rw [hid] at hdiv
      exact hdiv
    have hcoord (j : Fin N) :
        (2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2 * (d.u m j) ^ 2 ≤
          (d.g m j) ^ 2 := by
      have hu0 := phiSubgradient_coord_nonpos (d.u_subgradient m) j
      have hwu0 : d.weights m * d.u m j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (d.weights_nonneg m) hu0
      have hap0 : 0 ≤ d.a m * d.progressGrad m j :=
        mul_nonneg (d.a_nonneg m) (d.progressGrad_nonneg m j)
      have hsq : (d.weights m * d.u m j) ^ 2 ≤
          (d.weights m * d.u m j - d.a m * d.progressGrad m j) ^ 2 := by
        nlinarith
      calc
        (2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2 * (d.u m j) ^ 2 =
            (2 / (N : ℝ)) ^ 2 * (d.weights m * d.u m j) ^ 2 := by ring
        _ ≤ (2 / (N : ℝ)) ^ 2 *
            (d.weights m * d.u m j - d.a m * d.progressGrad m j) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = ((2 / (N : ℝ)) *
            (d.weights m * d.u m j - d.a m * d.progressGrad m j)) ^ 2 := by ring
        _ = (d.g m j) ^ 2 := by rw [d.g_eq]
    have hsum :
        ((2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2) *
            (∑ j, (d.u m j) ^ 2) ≤ ∑ j, (d.g m j) ^ 2 := by
      calc
        ((2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2) *
            (∑ j, (d.u m j) ^ 2) =
            ∑ j, (2 / (N : ℝ)) ^ 2 *
              (d.weights m) ^ 2 * (d.u m j) ^ 2 := by
          rw [Finset.mul_sum]
        _ ≤ ∑ j, (d.g m j) ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
    have hscale : 0 ≤ (2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hlower := mul_le_mul_of_nonneg_left hU hscale
    have hid :
        ((2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2) * ((N : ℝ) / 64) =
          (d.weights m) ^ 2 / (16 * (N : ℝ)) := by
      field_simp [ne_of_gt hNR]
      ring
    calc
      (d.weights m) ^ 2 / (16 * (N : ℝ)) =
          ((2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2) *
            ((N : ℝ) / 64) := hid.symm
      _ ≤ ((2 / (N : ℝ)) ^ 2 * (d.weights m) ^ 2) *
            (∑ j, (d.u m j) ^ 2) := hlower
      _ ≤ ∑ j, (d.g m j) ^ 2 := hsum

/-- The algebraic barrier of TeX lines 1945--1983. -/
theorem barrier_algebra {M N : Nat} (hN : 0 < N)
    (d : BarrierAlgebraData M N) :
    1 ≤ 16 * (N : ℝ) * blockSq d.g := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hblocks :
      (∑ m, (d.weights m) ^ 2 / (16 * (N : ℝ))) ≤ blockSq d.g := by
    unfold blockSq
    exact Finset.sum_le_sum fun m _ => barrier_block_lower hN d m
  have hone : 1 / (16 * (N : ℝ)) ≤ blockSq d.g := by
    calc
      1 / (16 * (N : ℝ)) =
          (∑ m, (d.weights m) ^ 2) / (16 * (N : ℝ)) := by
        rw [d.weights_sq_sum]
      _ = ∑ m, (d.weights m) ^ 2 / (16 * (N : ℝ)) := by
        rw [Finset.sum_div]
      _ ≤ blockSq d.g := hblocks
  have hden : (0 : ℝ) < 16 * (N : ℝ) := mul_pos (by norm_num) hNR
  have hfinal : 1 ≤ blockSq d.g * (16 * (N : ℝ)) :=
    (div_le_iff₀ hden).1 hone
  simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal

end

end WeaklyConvexLowerBound

