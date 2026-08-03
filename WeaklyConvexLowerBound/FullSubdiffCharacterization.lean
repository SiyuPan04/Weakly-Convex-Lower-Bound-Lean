import WeaklyConvexLowerBound.UnconditionalMain

/-!
# Variational characterization of the full hard subdifferential

`hardFormulaSet z` is the literal union over active outer weights appearing
in Lemma `lem:full-subdiff` of the manuscript.  This module proves the
all-point inclusion of its convex hull in the semantic `fullSubdiff`, and
the reverse inclusion (hence equality) whenever activation is positive.

The zero-activation reverse inclusion, compactness, and the final all-point
equality are completed in `ZeroActivationFullFormula`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set
open scoped BigOperators

/-- Literal union of the block-formula sets over all active outer weights. -/
def hardFormulaSet {M N : Nat} (z : BlockVec M N) : Set (BlockVec M N) :=
  {g | Nonempty (GeneralHardFormulaReply z g)}

/-! ## The zero-activation outer active set -/

/-- Zero activation is equivalent, coordinatewise, to having no positive
phase score. -/
theorem sigmaScore_nonpos_of_activationNorm_eq_zero {M N : Nat}
    {z : BlockVec M N} (hR0 : activationNorm z = 0) (m : Fin M) :
    sigmaScore z m ≤ 0 := by
  have hsum0 : (∑ i, (max (sigmaScore z i) 0) ^ 2) = 0 := by
    have hsumNonneg : 0 ≤ ∑ i, (max (sigmaScore z i) 0) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqrt := Real.sq_sqrt hsumNonneg
    unfold activationNorm at hR0
    rw [hR0] at hsqrt
    norm_num at hsqrt
    exact hsqrt.symm
  have hterm : (max (sigmaScore z m) 0) ^ 2 ≤
      ∑ i, (max (sigmaScore z i) 0) ^ 2 :=
    Finset.single_le_sum
      (fun i _ => sq_nonneg (max (sigmaScore z i) 0))
      (Finset.mem_univ m)
  rw [hsum0] at hterm
  have hmax : max (sigmaScore z m) 0 = 0 := by
    nlinarith [sq_nonneg (max (sigmaScore z m) 0)]
  exact max_eq_right_iff.mp hmax

/-- At zero activation, every positive active outer coordinate is supported
on an exactly zero score; negative scores receive zero weight.  Thus the
apparent degeneracy of the outer maximizer introduces no extra directions.
-/
theorem ActiveOuterWeight.score_eq_zero_of_activationNorm_eq_zero
    {M N : Nat} {z : BlockVec M N} {w : Fin M → ℝ}
    (hR0 : activationNorm z = 0) (hw : ActiveOuterWeight z w)
    (m : Fin M) (hwm : 0 < w m) :
    sigmaScore z m = 0 := by
  apply le_antisymm
  · exact sigmaScore_nonpos_of_activationNorm_eq_zero hR0 m
  · exact hw.score_nonneg_of_weight_ne_zero m hwm.ne'

theorem generalHardFormulaReply_blockDot {M N : Nat}
    {z g : BlockVec M N} (reply : GeneralHardFormulaReply z g)
    (y : BlockVec M N) :
    blockDot g (y - z) =
      (2 / (N : ℝ)) * ∑ m,
        (reply.w m * vecDot (reply.u m) (y m - z m) -
          netProgressWeight reply.w m *
            vecDot (psiGrad (z m)) (y m - z m)) := by
  classical
  unfold blockDot vecDot
  simp_rw [reply.g_eq]
  simp only [Pi.sub_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  calc
    (∑ x, (2 / (N : ℝ)) *
        (reply.w m * reply.u m x -
          (1 - nextOuterWeight reply.w m) * psiGrad (z m) x) *
          (y m x - z m x)) =
      ∑ x, (2 / (N : ℝ)) *
        (reply.w m * (reply.u m x * (y m x - z m x)) -
          netProgressWeight reply.w m *
            (psiGrad (z m) x * (y m x - z m x))) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [netProgressWeight]
      ring
    _ = (2 / (N : ℝ)) *
        ∑ x, (reply.w m * (reply.u m x * (y m x - z m x)) -
          netProgressWeight reply.w m *
            (psiGrad (z m) x * (y m x - z m x))) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Every vector in a fixed active block formula supports the fixed branch
with the sharp common quadratic coefficient `3/8`. -/
theorem GeneralHardFormulaReply.qSubgradient_activationBranch
    {M N : Nat} (hA : Admissible M N) {z g : BlockVec M N}
    (reply : GeneralHardFormulaReply z g) :
    QSubgradient (3 / 8 : ℝ) (activationBranch reply.w) z g := by
  intro y
  let a : Fin M → ℝ := netProgressWeight reply.w
  have hw := reply.active.1
  have hphi (m : Fin M) :
      vecDot (reply.u m) (y m - z m) ≤ phi (y m) - phi (z m) := by
    have h := phiSubgradient_to_vecConvexSubgradient (reply.u_subgradient m) (y m)
    linarith
  have hpsi (m : Fin M) :
      psi (y m) - psi (z m) ≤
        vecDot (psiGrad (z m)) (y m - z m) +
          (3 * (N : ℝ) / 16) * vecSq (y m - z m) := by
    have h := psi_descent hA.N_pos (z m) (y m)
    linarith
  have hterm (m : Fin M) :
      reply.w m * vecDot (reply.u m) (y m - z m) -
          a m * vecDot (psiGrad (z m)) (y m - z m) -
          a m * (3 * (N : ℝ) / 16) * vecSq (y m - z m) ≤
        reply.w m * (phi (y m) - phi (z m)) -
          a m * (psi (y m) - psi (z m)) := by
    have hw0 := hw.1 m
    have ha0 := netProgressWeight_nonneg hw m
    have hfan := mul_le_mul_of_nonneg_left (hphi m) hw0
    have hprog := mul_le_mul_of_nonneg_left (hpsi m) ha0
    dsimp [a]
    nlinarith
  have hsum := Finset.sum_le_sum
    (fun m (_ : m ∈ (Finset.univ : Finset (Fin M))) => hterm m)
  have ha1 (m : Fin M) : a m ≤ 1 :=
    netProgressWeight_le_one hw m
  have hquad :
      (2 / (N : ℝ)) * ∑ m,
          a m * (3 * (N : ℝ) / 16) * vecSq (y m - z m) ≤
        (3 / 8 : ℝ) * blockSq (y - z) := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
    have hblock : blockSq (y - z) =
        ∑ m, vecSq (y m - z m) := by rfl
    rw [hblock]
    have hweights : (∑ m,
        a m * (3 * (N : ℝ) / 16) * vecSq (y m - z m)) ≤
        ∑ m, (3 * (N : ℝ) / 16) * vecSq (y m - z m) := by
      apply Finset.sum_le_sum
      intro m _
      have hv : 0 ≤ vecSq (y m - z m) := by
        unfold vecSq
        exact Finset.sum_nonneg fun j _ => sq_nonneg _
      have hc : 0 ≤ 3 * (N : ℝ) / 16 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (ha1 m) (mul_nonneg hc hv)]
    have hs := mul_le_mul_of_nonneg_left hweights
      (by positivity : 0 ≤ 2 / (N : ℝ))
    calc
      _ ≤ (2 / (N : ℝ)) *
          ∑ m, (3 * (N : ℝ) / 16) * vecSq (y m - z m) := hs
      _ = (3 / 8 : ℝ) * ∑ m, vecSq (y m - z m) := by
        rw [← Finset.mul_sum]
        field_simp [hNreal.ne']; ring
  have hdot := generalHardFormulaReply_blockDot reply y
  have hbranch := activationBranch_sub_eq hA.M_pos reply.w y z
  have hsum' :
      (∑ m, (reply.w m * vecDot (reply.u m) (y m - z m) -
          netProgressWeight reply.w m *
            vecDot (psiGrad (z m)) (y m - z m))) -
        ∑ m, netProgressWeight reply.w m *
          (3 * (N : ℝ) / 16) * vecSq (y m - z m) ≤
      (∑ m, reply.w m * (phi (y m) - phi (z m))) -
        ∑ m, netProgressWeight reply.w m *
          (psi (y m) - psi (z m)) := by
    calc
      _ = ∑ m,
          ((reply.w m * vecDot (reply.u m) (y m - z m) -
              netProgressWeight reply.w m *
                vecDot (psiGrad (z m)) (y m - z m)) -
            netProgressWeight reply.w m *
              (3 * (N : ℝ) / 16) * vecSq (y m - z m)) := by
          symm
          apply Finset.sum_sub_distrib
      _ ≤ ∑ m, (reply.w m * (phi (y m) - phi (z m)) -
          netProgressWeight reply.w m * (psi (y m) - psi (z m))) := hsum
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hscaled := mul_le_mul_of_nonneg_left hsum'
    (by positivity : 0 ≤ 2 / (N : ℝ))
  have hmain :
      (2 / (N : ℝ)) *
          ∑ m, (reply.w m * vecDot (reply.u m) (y m - z m) -
            netProgressWeight reply.w m *
              vecDot (psiGrad (z m)) (y m - z m)) -
        (3 / 8 : ℝ) * blockSq (y - z) ≤
      (2 / (N : ℝ)) *
        ((∑ m, reply.w m * (phi (y m) - phi (z m))) -
          ∑ m, netProgressWeight reply.w m *
            (psi (y m) - psi (z m))) := by
    calc
      _ ≤ (2 / (N : ℝ)) *
          ∑ m, (reply.w m * vecDot (reply.u m) (y m - z m) -
            netProgressWeight reply.w m *
              vecDot (psiGrad (z m)) (y m - z m)) -
        (2 / (N : ℝ)) * ∑ m, netProgressWeight reply.w m *
          (3 * (N : ℝ) / 16) * vecSq (y m - z m) :=
            sub_le_sub_left hquad _
      _ = (2 / (N : ℝ)) *
          ((∑ m, (reply.w m * vecDot (reply.u m) (y m - z m) -
            netProgressWeight reply.w m *
              vecDot (psiGrad (z m)) (y m - z m))) -
          ∑ m, netProgressWeight reply.w m *
            (3 * (N : ℝ) / 16) * vecSq (y m - z m)) := by ring
      _ ≤ _ := hscaled
  change activationBranch reply.w z + blockDot g (y - z) -
      (3 / 8 : ℝ) * blockSq (y - z) ≤ activationBranch reply.w y
  rw [hdot]
  unfold branchFanDifference branchProgressDifference at hbranch
  calc
    _ ≤ activationBranch reply.w z +
        (2 / (N : ℝ)) *
          ((∑ m, reply.w m * (phi (y m) - phi (z m))) -
            ∑ m, netProgressWeight reply.w m *
              (psi (y m) - psi (z m))) :=
      by nlinarith [hmain]
    _ = activationBranch reply.w y := by nlinarith

/-- Every displayed formula vector is a semantic full subgradient of the
hard value, including at zero activation. -/
theorem GeneralHardFormulaReply.mem_fullSubdiff
    {M N : Nat} (hA : Admissible M N) {z g : BlockVec M N}
    (reply : GeneralHardFormulaReply z g) :
    g ∈ fullSubdiff 1 (@hardValue M N) z := by
  have hbranch := reply.qSubgradient_activationBranch hA
  have hcontact : activationBranch reply.w z = hardValue z := by
    unfold activationBranch hardValue
    rw [reply.active.2]
  have hq : QSubgradient (3 / 8 : ℝ) (@hardValue M N) z g := by
    intro y
    have hsupp := hbranch y
    have hdom := activationBranch_le_hardValue hA.N_pos
      reply.active.1 y
    rw [hcontact] at hsupp
    exact hsupp.trans hdom
  rw [mem_fullSubdiff_iff_qSubgradient]
  exact hq.mono (by norm_num)

theorem hardFormulaSet_subset_fullSubdiff {M N : Nat}
    (hA : Admissible M N) (z : BlockVec M N) :
    hardFormulaSet z ⊆ fullSubdiff 1 (@hardValue M N) z := by
  intro g hg
  exact Classical.choice hg |>.mem_fullSubdiff hA

/-- A full quadratic-support reply set is convex in its vector argument. -/
theorem fullSubdiff_convex {M N : Nat} (rho : ℝ)
    (f : BlockVec M N → ℝ) (z : BlockVec M N) :
    Convex ℝ (fullSubdiff rho f z) := by
  intro g hg h hh a b ha hb hab
  rw [mem_fullSubdiff_iff_qSubgradient] at hg hh ⊢
  intro y
  have hgy := hg y
  have hhy := hh y
  rw [blockDot_add_left, blockDot_smul_left', blockDot_smul_left']
  have hcomb := add_le_add
    (mul_le_mul_of_nonneg_left hgy ha)
    (mul_le_mul_of_nonneg_left hhy hb)
  have hleft :
      a * (f z + blockDot g (y - z) -
          rho / 2 * blockSq (y - z)) +
        b * (f z + blockDot h (y - z) -
          rho / 2 * blockSq (y - z)) =
      f z + (a * blockDot g (y - z) + b * blockDot h (y - z)) -
        rho / 2 * blockSq (y - z) := by
    calc
      _ = (a + b) * f z +
          (a * blockDot g (y - z) + b * blockDot h (y - z)) -
          (a + b) * (rho / 2 * blockSq (y - z)) := by ring
      _ = _ := by rw [hab]; ring
  have hright : a * f y + b * f y = f y := by
    rw [← add_mul, hab, one_mul]
  rw [hleft, hright] at hcomb
  exact hcomb

/-- The manuscript's right-hand side is always contained in the semantic
full subdifferential. -/
theorem convexHull_hardFormulaSet_subset_fullSubdiff {M N : Nat}
    (hA : Admissible M N) (z : BlockVec M N) :
    convexHull ℝ (hardFormulaSet z) ⊆
      fullSubdiff 1 (@hardValue M N) z := by
  exact convexHull_min (hardFormulaSet_subset_fullSubdiff hA z)
    (fullSubdiff_convex 1 hardValue z)

/-- At positive activation the outer maximizer is unique, and the already
proved semantic reconstruction gives the reverse inclusion without taking a
convex hull. -/
theorem fullSubdiff_subset_hardFormulaSet_of_activation_pos {M N : Nat}
    (hA : Admissible M N) {z : BlockVec M N}
    (hR : 0 < activationNorm z) :
    fullSubdiff 1 (@hardValue M N) z ⊆ hardFormulaSet z := by
  intro g hg
  exact ⟨(fullSubdiff_one_positive_hardFormulaReply hA hR hg).toGeneral⟩

/-- Exact form of Lemma `lem:full-subdiff` away from the zero-activation
stratum. -/
theorem fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_pos
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (hR : 0 < activationNorm z) :
    fullSubdiff 1 (@hardValue M N) z = convexHull ℝ (hardFormulaSet z) := by
  apply Set.Subset.antisymm
  · intro g hg
    exact subset_convexHull ℝ (hardFormulaSet z)
      (fullSubdiff_subset_hardFormulaSet_of_activation_pos hA hR hg)
  · exact convexHull_hardFormulaSet_subset_fullSubdiff hA z

end

end WeaklyConvexLowerBound

