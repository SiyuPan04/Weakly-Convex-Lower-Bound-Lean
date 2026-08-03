import WeaklyConvexLowerBound.CoreFunctions
import WeaklyConvexLowerBound.Progress

/-!
# The normalized hard value

This file assembles the block relay from the tilted fan and the smooth
progress carrier.  It verifies the terminal-activation argument and the
initial-gap arithmetic of the weakly convex lower-bound manuscript.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The first coordinate, made explicit so that `N > 0` is visible in every
use of the distinguished facet. -/
def firstCoord {N : Nat} (hN : 0 < N) : Fin N := ⟨0, hN⟩

/-- The first block. -/
def firstBlock {M : Nat} (hM : 0 < M) : Fin M := ⟨0, hM⟩

/-- The terminal block. -/
def lastBlock {M : Nat} (hM : 0 < M) : Fin M := ⟨M - 1, by omega⟩

/-- Progress immediately before block `m`; zero-based block zero receives the
paper's initialization value one. -/
def previousProgress {M N : Nat} (z : BlockVec M N) (m : Fin M) : ℝ :=
  if hm : m.1 = 0 then 1
  else psi (z ⟨m.1 - 1, by omega⟩)

/-- The phase score `sigma_m`. -/
def sigmaScore {M N : Nat} (z : BlockVec M N) (m : Fin M) : ℝ :=
  phi (z m) + previousProgress z m - 5 / 4

/-- Euclidean norm of the coordinatewise positive part of the phase scores. -/
def activationNorm {M N : Nat} (z : BlockVec M N) : ℝ :=
  Real.sqrt (∑ m, (max (sigmaScore z m) 0) ^ 2)

/-- The normalized hard instance from equation `eq:hard`. -/
def hardValue {M N : Nat} (z : BlockVec M N) : ℝ :=
  2 / (N : ℝ) * (activationNorm z - ∑ m, psi (z m))

@[simp] theorem psi_zero (N : Nat) : psi (0 : Fin N → ℝ) = 0 := by
  simp [psi]

/-! ## The fan at the origin -/

/-- At the origin the first affine facet is active, so the fan value is its
intercept. -/
theorem phi_zero_eq_intercept_first {N : Nat} (hN : 0 < N) :
    phi (0 : Fin N → ℝ) = intercept N (firstCoord hN) := by
  let i : Fin N := firstCoord hN
  have hactive : ActiveFacet (0 : Fin N → ℝ) (some i) := by
    rw [activeFacet_iff_maximal]
    intro r
    cases r with
    | none =>
        simp only [facetValue_none, facetValue_some, Pi.zero_apply, mul_zero,
          sub_zero]
        linarith [intercept_ge_one hN i]
    | some j =>
        simp only [facetValue_some, Pi.zero_apply, mul_zero, sub_zero]
        by_cases hji : j = i
        · simp [hji]
        · have hjval : j.1 ≠ 0 := by
            intro hj0
            apply hji
            apply Fin.ext
            simpa [i, firstCoord] using hj0
          have hij : i.1 < j.1 := by
            dsimp [i, firstCoord]
            omega
          exact (intercept_strictAnti hN hij).le
  unfold ActiveFacet at hactive
  simpa [i, firstCoord] using hactive.symm

theorem intercept_first_lt_five_fourths {N : Nat} (hN : 0 < N) :
    intercept N (firstCoord hN) < (5 : ℝ) / 4 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < (16 : ℝ) * N := by positivity
  have hfrac : ((N : ℝ) - 1) / (16 * (N : ℝ)) < (1 : ℝ) / 4 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  calc
    intercept N (firstCoord hN) =
        1 + ((N : ℝ) - 1) / (16 * (N : ℝ)) := by
      simp [intercept, firstCoord]
    _ < 1 + (1 : ℝ) / 4 := by
      simpa [add_comm] using add_lt_add_left hfrac 1
    _ = (5 : ℝ) / 4 := by norm_num

/-! ## Positive activation -/

theorem activationNorm_nonneg {M N : Nat} (z : BlockVec M N) :
    0 ≤ activationNorm z := Real.sqrt_nonneg _

theorem activationNorm_pos_of_sigmaScore_pos {M N : Nat}
    {z : BlockVec M N} {m : Fin M} (hm : 0 < sigmaScore z m) :
    0 < activationNorm z := by
  unfold activationNorm
  apply Real.sqrt_pos.2
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg (max (sigmaScore z i) 0)
  · refine ⟨m, Finset.mem_univ m, ?_⟩
    rw [max_eq_left hm.le]
    exact sq_pos_of_pos hm

/-- If terminal progress is below `q(3/4)=27/32`, choose the first block
below that threshold.  Its predecessor is above the threshold, while one of
its coordinates is still below `3/4`; hence its phase score is positive. -/
theorem terminal_activation {M N : Nat} (hM : 0 < M) (hN : 0 < N)
    (z : BlockVec M N)
    (hterminal : psi (z (lastBlock hM)) < (27 : ℝ) / 32) :
    0 < activationNorm z := by
  let lowAt : Nat → Prop := fun k ↦
    ∃ hk : k < M, psi (z ⟨k, hk⟩) < (27 : ℝ) / 32
  have hex : ∃ k, lowAt k := by
    refine ⟨M - 1, by omega, ?_⟩
    simpa [lastBlock] using hterminal
  let k := Nat.find hex
  have hkspec : lowAt k := Nat.find_spec hex
  rcases hkspec with ⟨hkM, hkcur⟩
  let mhat : Fin M := ⟨k, hkM⟩
  have hcur : psi (z mhat) < (27 : ℝ) / 32 := by
    simpa [mhat] using hkcur
  have hprev : (27 : ℝ) / 32 ≤ previousProgress z mhat := by
    by_cases hk0 : k = 0
    · have hmhat0 : mhat.1 = 0 := by
        simpa only [mhat, Fin.val_mk] using hk0
      simp only [previousProgress, dif_pos hmhat0]
      norm_num
    · have hkpred : k - 1 < k := by omega
      have hkpredM : k - 1 < M := by omega
      have hnotlow : ¬ psi (z ⟨k - 1, hkpredM⟩) < (27 : ℝ) / 32 := by
        intro hlow
        exact (Nat.find_min hex hkpred) ⟨hkpredM, hlow⟩
      have hge : (27 : ℝ) / 32 ≤ psi (z ⟨k - 1, hkpredM⟩) :=
        le_of_not_gt hnotlow
      have hmhat0 : mhat.1 ≠ 0 := by
        simpa only [mhat, Fin.val_mk] using hk0
      simp only [previousProgress, dif_neg hmhat0]
      simpa only [mhat, Fin.val_mk] using hge
  have hexcoord : ∃ j : Fin N,
      (N : ℝ) * z mhat j / 4 < (3 : ℝ) / 4 := by
    by_contra hnone
    have hall : ∀ j : Fin N,
        (3 : ℝ) / 4 ≤ (N : ℝ) * z mhat j / 4 := by
      intro j
      exact le_of_not_gt (fun hj ↦ hnone ⟨j, hj⟩)
    have hsum : (∑ _j : Fin N, ((27 : ℝ) / 32)) ≤
        ∑ j, q ((N : ℝ) * z mhat j / 4) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        (27 : ℝ) / 32 = q ((3 : ℝ) / 4) := q_three_quarters.symm
        _ ≤ q ((N : ℝ) * z mhat j / 4) := q_monotone (hall j)
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have havg : (27 : ℝ) / 32 ≤ psi (z mhat) := by
      unfold psi
      rw [le_div_iff₀ hNreal]
      simpa [mul_comm] using hsum
    exact (not_lt_of_ge havg) hcur
  obtain ⟨j, hj⟩ := hexcoord
  have htilt : (N : ℝ) / 8 * z mhat j < (3 : ℝ) / 8 := by
    nlinarith
  have hfacet : (5 : ℝ) / 8 < facetValue (z mhat) (some j) := by
    rw [facetValue_some]
    nlinarith [intercept_ge_one hN j]
  have hphi : (5 : ℝ) / 8 < phi (z mhat) :=
    hfacet.trans_le (facetValue_le_phi (z mhat) (some j))
  have hscore : 0 < sigmaScore z mhat := by
    unfold sigmaScore
    nlinarith
  exact activationNorm_pos_of_sigmaScore_pos hscore

/-! ## Lower bound and initial gap -/

/-- The nonnegative activation term and `psi ≤ 1` give the paper's global
lower bound. -/
theorem hardValue_lower {M N : Nat} (hN : 0 < N) (z : BlockVec M N) :
    -(2 * (M : ℝ) / (N : ℝ)) ≤ hardValue z := by
  have hsum : (∑ m, psi (z m)) ≤ ∑ _m : Fin M, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro m _
    exact psi_le_one hN (z m)
  have hsumM : (∑ m, psi (z m)) ≤ (M : ℝ) := by
    simpa using hsum
  have hinside : -(M : ℝ) ≤ activationNorm z - ∑ m, psi (z m) := by
    have hR := activationNorm_nonneg z
    linarith
  unfold hardValue
  calc
    -(2 * (M : ℝ) / (N : ℝ)) =
        (2 / (N : ℝ)) * (-(M : ℝ)) := by ring
    _ ≤ (2 / (N : ℝ)) * (activationNorm z - ∑ m, psi (z m)) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)

theorem hardValue_range_bddBelow {M N : Nat} (hN : 0 < N) :
    BddBelow (Set.range (@hardValue M N)) := by
  refine ⟨-(2 * (M : ℝ) / (N : ℝ)), ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hardValue_lower hN z

/-- At zero only the first phase score has positive part. -/
theorem activationNorm_zero_lt_one {M N : Nat}
    (hM : 2 ≤ M) (hN : 0 < N) :
    activationNorm (0 : BlockVec M N) < 1 := by
  have hMpos : 0 < M := by omega
  let i : Fin M := firstBlock hMpos
  let c : ℝ := intercept N (firstCoord hN)
  have hc1 : 1 ≤ c := intercept_ge_one hN (firstCoord hN)
  have hc5 : c < (5 : ℝ) / 4 := intercept_first_lt_five_fourths hN
  have hfirst : sigmaScore (0 : BlockVec M N) i = c + 1 - 5 / 4 := by
    unfold sigmaScore
    rw [show (0 : BlockVec M N) i = (0 : Fin N → ℝ) by rfl]
    rw [phi_zero_eq_intercept_first hN]
    simp [previousProgress, i, firstBlock, c]
  have hfirstpos : 0 < sigmaScore (0 : BlockVec M N) i := by
    rw [hfirst]
    linarith
  have hfirstlt : sigmaScore (0 : BlockVec M N) i < 1 := by
    rw [hfirst]
    linarith
  have hother : ∀ m : Fin M, m ≠ i →
      sigmaScore (0 : BlockVec M N) m < 0 := by
    intro m hmi
    have hm0 : m.1 ≠ 0 := by
      intro hmval
      apply hmi
      apply Fin.ext
      simpa [i, firstBlock] using hmval
    unfold sigmaScore
    rw [show (0 : BlockVec M N) m = (0 : Fin N → ℝ) by rfl]
    rw [phi_zero_eq_intercept_first hN]
    simp only [previousProgress, dif_neg hm0, Pi.zero_apply, psi_zero]
    dsimp [c] at hc5
    linarith
  have hsum : (∑ m : Fin M,
      (max (sigmaScore (0 : BlockVec M N) m) 0) ^ 2) =
      sigmaScore (0 : BlockVec M N) i ^ 2 := by
    classical
    rw [Finset.sum_eq_single i]
    · rw [max_eq_left hfirstpos.le]
    · intro m _ hmi
      rw [max_eq_right (hother m hmi).le]
      norm_num
    · simp
  unfold activationNorm
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hfirstpos]
  exact hfirstlt

theorem hardValue_zero_lt_two_div_N {M N : Nat}
    (hM : 2 ≤ M) (hN : 0 < N) :
    hardValue (0 : BlockVec M N) < 2 / (N : ℝ) := by
  have hR := activationNorm_zero_lt_one hM hN
  have hsum : (∑ m : Fin M, psi ((0 : BlockVec M N) m)) = 0 := by
    simp
  unfold hardValue
  rw [hsum, sub_zero]
  have hscale : 0 < 2 / (N : ℝ) := by positivity
  simpa using mul_lt_mul_of_pos_left hR hscale

/-- Condition (C4): the origin-to-infimum gap is at most `3 M / N`. -/
theorem hardValue_initial_gap_le {M N : Nat}
    (hM : 2 ≤ M) (hN : 0 < N) :
    hardValue (0 : BlockVec M N) -
        sInf (Set.range (@hardValue M N)) ≤ 3 * (M : ℝ) / (N : ℝ) := by
  have hinf : -(2 * (M : ℝ) / (N : ℝ)) ≤
      sInf (Set.range (@hardValue M N)) := by
    rw [le_csInf_iff (hardValue_range_bddBelow (M := M) hN)
      (Set.range_nonempty _)]
    rintro _ ⟨z, rfl⟩
    exact hardValue_lower hN z
  have hzero := hardValue_zero_lt_two_div_N hM hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have harith : 2 / (N : ℝ) + 2 * (M : ℝ) / (N : ℝ) ≤
      3 * (M : ℝ) / (N : ℝ) := by
    rw [← add_div, div_le_div_iff_of_pos_right hNreal]
    nlinarith
  linarith

end

end WeaklyConvexLowerBound

