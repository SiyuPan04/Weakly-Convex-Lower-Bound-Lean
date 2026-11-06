import WC.CoupledSubgradient

/-! Actual raw subgradients vanish on coordinates beyond the completed plateau. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem coupledFacetBranchGradient_apply {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (a : Fin M → FanFacet N) (x : ChainSpace M N) (m : Fin M) (n : Fin N) :
    coupledFacetBranchGradient w a x (m, n) =
      (2 / (N : ℝ)) * blockFacetGradient w a m (euclideanBlock x m) n := by
  simp [coupledFacetBranchGradient, embedBlockGradient, eq_comm]

theorem progressGradient_zero_of_large {N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin N)) (n : Fin N) (hn : 9 / (N : ℝ) < x n) :
    progressGradient x n = 0 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have heq : (N : ℝ) / 4 * (9 / (N : ℝ)) = 9 / 4 := by field_simp
  have ht : 1 / (64 * (N : ℝ)) ≤ 1 :=
    (div_le_iff₀ (by positivity : 0 < 64 * (N : ℝ))).mpr (by nlinarith)
  have hm := mul_lt_mul_of_pos_left hn (show 0 < (N : ℝ) / 4 by positivity)
  have harg : 1 ≤ (N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ)) := by nlinarith [heq]
  have hargpos : 0 < (N : ℝ) / 4 * x n - 1 / (64 * (N : ℝ)) := by linarith
  change progressGateSlope _ / 4 = 0
  unfold progressGateSlope
  rw [if_neg (not_le.mpr hargpos), if_neg (not_lt.mpr harg)]
  norm_num

theorem activeFacet_weighted_gap_zero {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) (hactive : coupledFacetBranch w a x = coupledFunction x) (m : Fin M) :
    w m * (euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) -
      affineFacet N (M * N) m.val (a m) (euclideanBlock x m)) = 0 := by
  have hwb : weightedCoupledFunction w x = coupledFacetBranch w a x := by
    exact le_antisymm ((weightedCoupledFunction_le w x hw).trans (le_of_eq hactive.symm))
      (coupledFacetBranch_le_weightedCoupledFunction w hw a x)
  let gap (j : Fin M) := w j * (euclideanTiltedBlock N (M * N) j.val (euclideanBlock x j) -
    affineFacet N (M * N) j.val (a j) (euclideanBlock x j))
  have hgap (j : Fin M) : 0 ≤ gap j := mul_nonneg (hw.1 j)
    (sub_nonneg.mpr (affineFacet_le_tiltedBlock N (M * N) j.val (a j) (euclideanBlock x j)))
  have heq : weightedCoupledFunction w x - coupledFacetBranch w a x =
      (2 / (N : ℝ)) * ∑ j, gap j := by
    rw [weightedCoupledFunction_grouped]
    simp only [coupledFacetBranch, gap, euclideanTiltedBlock, euclideanBlock,
      Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hwb, sub_self] at heq
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ j, gap j = 0 :=
    (mul_eq_zero.mp heq.symm).resolve_left (ne_of_gt (by positivity : 0 < 2 / (N : ℝ)))
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hgap j) (Finset.mem_univ m)
  rw [hsum] at hle
  exact le_antisymm hle (hgap m)

theorem activeFacetBranchGradient_zero_of_large {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) (hactive : coupledFacetBranch w a x = coupledFunction x)
    (m : Fin M) (n : Fin N) (hn : 9 / (N : ℝ) < x (m, n)) :
    coupledFacetBranchGradient w a x (m, n) = 0 := by
  rw [coupledFacetBranchGradient_apply]
  have hprog : progressGradient (euclideanBlock x m) n = 0 := progressGradient_zero_of_large hN _ n hn
  have hfan : w m * affineFacetGradient N (a m) n = 0 := by
    cases ha : a m with
    | none => simp [affineFacetGradient]
    | some j =>
      by_cases hjn : n = j
      · subst n
        have hpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hc := tiltIntercept_lt (K := M * N) (r := m.val * N + j.val)
        have hm := mul_lt_mul_of_pos_left hn (show 0 < (N : ℝ) / 8 by positivity)
        have heq : (N : ℝ) / 8 * (9 / (N : ℝ)) = 9 / 8 := by field_simp
        have hfacet : affineFacet N (M * N) m.val (a m) (euclideanBlock x m) < 0 := by
          simp only [ha, affineFacet, euclideanBlock, coupledBlock]
          nlinarith [heq]
        have hgap := activeFacet_weighted_gap_zero hN w hw a x hactive m
        have hd : 0 < euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) -
            affineFacet N (M * N) m.val (a m) (euclideanBlock x m) :=
          sub_pos.mpr (lt_of_lt_of_le hfacet (tiltedBlock_nonneg N (M * N) m.val _))
        have hwzero : w m = 0 := (mul_eq_zero.mp hgap).resolve_right (ne_of_gt hd)
        simp [hwzero]
      · simp [affineFacetGradient, hjn]
  simp only [blockFacetGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    smoothBlockGradient, hprog, mul_zero, add_zero]
  rw [hfan, mul_zero]

/-- Every member of the entire actual raw subdifferential has the saturation support property. -/
theorem coupledFunction_subgradient_zero_of_large {M N : ℕ} (hN : 0 < N)
    {x v : ChainSpace M N} (hv : v ∈ subdifferential coupledFunction x)
    (i : Fin M × Fin N) (hi : 9 / (N : ℝ) < x i) : v i = 0 := by
  rw [subdifferential_coupledFunction_eq_convexHull hN] at hv
  have hconv : Convex ℝ {g : ChainSpace M N | g i = 0} := by
    intro g hg h hh a b _ _ _
    change g i = 0 at hg
    change h i = 0 at hh
    change a * g i + b * h i = 0
    simp [hg, hh]
  have hsub : coupledActiveGradients x ⊆ {g : ChainSpace M N | g i = 0} := by
    rintro g ⟨w, hw, a, hactive, rfl⟩
    exact activeFacetBranchGradient_zero_of_large hN w hw a x hactive i.1 i.2 hi
  exact (convexHull_min hsub hconv) hv

end WC
