import WC.FanSubdifferential
import WC.SaturatedSubgradient
import Mathlib.Analysis.Convex.Combination

/-! The manuscript's blockwise characterization of the complete raw
subdifferential, regrouped from the exact smooth-facet maximum rule. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

def coupledGradientLinear {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) :
    (Fin M → EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ChainSpace M N where
  toFun := fun u => WithLp.toLp 2 (fun i => (2 / (N : ℝ)) * (w i.1 * u i.1 i.2))
  map_add' u v := by
    apply PiLp.ext
    intro i
    simp only [Pi.add_apply, PiLp.add_apply]
    ring
  map_smul' a u := by
    apply PiLp.ext
    intro i
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def coupledGradientAssembly {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    (Fin M → EuclideanSpace ℝ (Fin N)) →ᵃ[ℝ] ChainSpace M N where
  toFun := fun u => WithLp.toLp 2 (fun i => (2 / (N : ℝ)) *
    (w i.1 * u i.1 i.2 + smoothBlockGradient (nextWeight w i.1) (euclideanBlock x i.1) i.2))
  linear := coupledGradientLinear w
  map_vadd' u v := by
    apply PiLp.ext
    intro i
    change (2 / (N : ℝ)) * (w i.1 * (v i.1 i.2 + u i.1 i.2) + _) =
      (2 / (N : ℝ)) * (w i.1 * v i.1 i.2) + (2 / (N : ℝ)) * (w i.1 * u i.1 i.2 + _)
    ring

@[simp] theorem coupledGradientAssembly_apply {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (x : ChainSpace M N) (u : Fin M → EuclideanSpace ℝ (Fin N)) (i : Fin M × Fin N) :
    coupledGradientAssembly w x u i = (2 / (N : ℝ)) *
      (w i.1 * u i.1 i.2 + smoothBlockGradient (nextWeight w i.1) (euclideanBlock x i.1) i.2) := rfl

theorem coupledGradientAssembly_facets {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (x : ChainSpace M N) (a : Fin M → FanFacet N) :
    coupledGradientAssembly w x (fun m => affineFacetGradient N (a m)) = coupledFacetBranchGradient w a x := by
  apply PiLp.ext
  rintro ⟨m, n⟩
  rw [coupledGradientAssembly_apply, coupledFacetBranchGradient_apply]
  rfl

def coupledBlockSubgradients {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    Set (ChainSpace M N) := coupledGradientAssembly w x '' Set.pi Set.univ
      (fun m => subdifferential (euclideanTiltedBlock N (M * N) m.val) (euclideanBlock x m))

def coupledProgressCoefficient {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N)
    (m : Fin M) : ℝ := 2 - nextWeight w m * relaySlope (euclideanProgress (euclideanBlock x m))

theorem mem_coupledBlockSubgradients_iff {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (x g : ChainSpace M N) : g ∈ coupledBlockSubgradients w x ↔
    ∃ u : Fin M → EuclideanSpace ℝ (Fin N),
      (∀ m, u m ∈ subdifferential (euclideanTiltedBlock N (M * N) m.val) (euclideanBlock x m)) ∧
      ∀ m, euclideanBlock g m = (2 / (N : ℝ)) •
        (w m • u m - coupledProgressCoefficient w x m • progressGradient (euclideanBlock x m)) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, fun m => hu m (Set.mem_univ m), ?_⟩
    intro m
    apply PiLp.ext
    intro n
    change (2 / (N : ℝ)) * (w m * u m n + smoothBlockGradient (nextWeight w m) (euclideanBlock x m) n) = _
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, smoothBlockGradient,
      coupledProgressCoefficient]
    ring
  · rintro ⟨u, hu, hg⟩
    refine ⟨u, fun m _ => hu m, ?_⟩
    apply PiLp.ext
    rintro ⟨m, n⟩
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v n) (hg m)
    change g (m, n) = (2 / (N : ℝ)) *
      (w m * u m n - coupledProgressCoefficient w x m * progressGradient (euclideanBlock x m) n) at hh
    rw [coupledGradientAssembly_apply, hh]
    simp only [smoothBlockGradient, PiLp.smul_apply, smul_eq_mul, coupledProgressCoefficient]
    ring

def regroupedCoupledGradients {M N : ℕ} (x : ChainSpace M N) : Set (ChainSpace M N) :=
  {g | ∃ (w : EuclideanSpace ℝ (Fin M)), w ∈ scoreWeights ∧
    weightedCoupledFunction w x = coupledFunction x ∧ g ∈ coupledBlockSubgradients w x}

theorem coupledActiveGradients_subset_regrouped {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    coupledActiveGradients x ⊆ regroupedCoupledGradients x := by
  rintro g ⟨w, hw, a, hactive, rfl⟩
  have hweight : weightedCoupledFunction w x = coupledFunction x :=
    le_antisymm (weightedCoupledFunction_le w x hw)
      (hactive ▸ coupledFacetBranch_le_weightedCoupledFunction w hw a x)
  choose b hb using fun m : Fin M => affineFacet_attains_tiltedBlock N (M * N) m.val (euclideanBlock x m)
  let a' : Fin M → FanFacet N := fun m => if w m = 0 then b m else a m
  have ha' (m : Fin M) : affineFacet N (M * N) m.val (a' m) (euclideanBlock x m) =
      euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) := by
    dsimp only [a']
    split_ifs with hm
    · exact hb m
    · have hgap := activeFacet_weighted_gap_zero hN w hw a x hactive m
      have hz := (mul_eq_zero.mp hgap).resolve_left hm
      linarith
  have hu (m : Fin M) : affineFacetGradient N (a' m) ∈
      subdifferential (euclideanTiltedBlock N (M * N) m.val) (euclideanBlock x m) := by
    rw [subdifferential_euclideanTiltedBlock_eq_convexHull]
    exact subset_convexHull ℝ _ ⟨a' m, ha' m, rfl⟩
  have hgrad : coupledGradientAssembly w x (fun m => affineFacetGradient N (a' m)) =
      coupledFacetBranchGradient w a x := by
    apply PiLp.ext
    rintro ⟨m, n⟩
    rw [coupledGradientAssembly_apply, coupledFacetBranchGradient_apply]
    change (2 / (N : ℝ)) * (w m * affineFacetGradient N (a' m) n + _) =
      (2 / (N : ℝ)) * (w m * affineFacetGradient N (a m) n + _)
    by_cases hm : w m = 0
    · simp [hm]
    · simp only [a', if_neg hm]
      rfl
  exact ⟨w, hw, hweight, ⟨fun m => affineFacetGradient N (a' m), fun m _ => hu m, hgrad⟩⟩

theorem coupledBlockSubgradients_subset_convexHull {M N : ℕ}
    (x : ChainSpace M N) (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (hweight : weightedCoupledFunction w x = coupledFunction x) :
    coupledBlockSubgradients w x ⊆ convexHull ℝ (coupledActiveGradients x) := by
  rintro g ⟨u, hu, rfl⟩
  let A : Fin M → Set (EuclideanSpace ℝ (Fin N)) := fun m =>
    fanActiveGradients N (M * N) m.val (euclideanBlock x m)
  have hprod : u ∈ convexHull ℝ (Set.pi Set.univ A) := by
    apply mem_convexHull_pi
    intro m _
    exact (subdifferential_euclideanTiltedBlock_eq_convexHull N (M * N) m.val (euclideanBlock x m)) ▸
      hu m (Set.mem_univ m)
  have himage : coupledGradientAssembly w x '' Set.pi Set.univ A ⊆ coupledActiveGradients x := by
    rintro g ⟨v, hv, rfl⟩
    choose a ha hg using fun m : Fin M => hv m (Set.mem_univ m)
    have hactive : coupledFacetBranch w a x = coupledFunction x := by
      rw [← hweight, weightedCoupledFunction_grouped]
      unfold coupledFacetBranch
      simp only [ha]
      rfl
    have hvg : v = fun m => affineFacetGradient N (a m) := by funext m; exact hg m
    rw [hvg, coupledGradientAssembly_facets]
    exact ⟨w, hw, a, hactive, rfl⟩
  have hg : coupledGradientAssembly w x u ∈ convexHull ℝ (coupledGradientAssembly w x '' Set.pi Set.univ A) := by
    rw [← (coupledGradientAssembly w x).image_convexHull]
    exact ⟨u, hprod, rfl⟩
  exact convexHull_mono himage hg

/-- The literal blockwise complete-subdifferential formula of
Lemma `full-subdiff`: the outer hull ranges over all active score weights,
and each block fan subgradient ranges over its entire genuine set. -/
theorem subdifferential_coupledFunction_eq_regrouped {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    subdifferential coupledFunction x = convexHull ℝ (regroupedCoupledGradients x) := by
  rw [subdifferential_coupledFunction_eq_convexHull hN]
  apply Set.Subset.antisymm
  · exact convexHull_mono (coupledActiveGradients_subset_regrouped hN x)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro g ⟨w, hw, hweight, hg⟩
    exact coupledBlockSubgradients_subset_convexHull x w hw hweight hg

theorem euclideanTiltedBlock_global_lipschitz (N K m : ℕ) :
    GloballyLipschitz ((N : ℝ) / 8) (euclideanTiltedBlock N K m) := by
  have h := compactMaximum_lipschitz (fanParameterizedBranch_joint_continuous N K m)
    (fun a : FacetTuples 1 N => affineFacet_lipschitz N K m (a 0))
  rwa [compactMaximum_fanParameterizedBranch] at h

theorem euclideanTiltedBlock_weaklyConvex_zero (N K m : ℕ) :
    WeaklyConvex 0 (euclideanTiltedBlock N K m) := by
  simpa only [WeaklyConvex, zero_div, zero_mul, add_zero] using convexOn_euclideanTiltedBlock N K m

theorem coupledBlockSubgradients_nonempty {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    (coupledBlockSubgradients w x).Nonempty := by
  choose a ha using fun m : Fin M => affineFacet_attains_tiltedBlock N (M * N) m.val (euclideanBlock x m)
  refine ⟨coupledGradientAssembly w x (fun m => affineFacetGradient N (a m)),
    fun m => affineFacetGradient N (a m), ?_, rfl⟩
  intro m _
  change affineFacetGradient N (a m) ∈
    subdifferential (euclideanTiltedBlock N (M * N) m.val) (euclideanBlock x m)
  rw [subdifferential_euclideanTiltedBlock_eq_convexHull]
  exact subset_convexHull ℝ _ ⟨a m, ha m, rfl⟩

theorem coupledBlockSubgradients_convex {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    Convex ℝ (coupledBlockSubgradients w x) := by
  apply Convex.affine_image
  apply convex_pi
  intro m _
  exact subdifferential_convex (euclideanBlock x m) (by norm_num)
    (euclideanTiltedBlock_weaklyConvex_zero N (M * N) m.val)

theorem coupledGradientAssembly_continuous {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    Continuous (coupledGradientAssembly w x) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin M × Fin N => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul ((continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i.2).comp (continuous_apply i.1))).add continuous_const)

theorem coupledBlockSubgradients_isCompact {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    IsCompact (coupledBlockSubgradients w x) := by
  apply IsCompact.image _ (coupledGradientAssembly_continuous w x)
  apply isCompact_univ_pi
  intro m
  exact subdifferential_isCompact (euclideanBlock x m) (by positivity : (0 : ℝ) ≤ (N : ℝ) / 8)
    (by norm_num : (0 : ℝ) ≤ 0) (euclideanTiltedBlock_global_lipschitz N (M * N) m.val)
    (euclideanTiltedBlock_weaklyConvex_zero N (M * N) m.val)

theorem coupledProgressCoefficient_mem_Icc {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (hw : w ∈ scoreWeights) (x : ChainSpace M N) (m : Fin M) :
    coupledProgressCoefficient w x m ∈ Set.Icc (0 : ℝ) 2 := by
  have hω0 := nextWeight_nonneg hw m
  have hω1 := nextWeight_le_one hw m
  have hs0 := relaySlope_nonneg (euclideanProgress (euclideanBlock x m))
  have hs1 := relaySlope_le (euclideanProgress (euclideanBlock x m))
  have hlo := mul_nonneg hω0 hs0
  have hhi := mul_le_mul_of_nonneg_right hω1 hs0
  dsimp only [coupledProgressCoefficient, Set.mem_Icc]
  constructor <;> linarith

theorem active_score_weight_nonneg {ι : Type*} [Fintype ι]
    (s w : EuclideanSpace ℝ ι) (hw : w ∈ scoreWeights)
    (hattain : inner ℝ w s = ‖positiveScores s‖) (m : ι) (hwm : 0 < w m) : 0 ≤ s m := by
  by_contra hnot
  have hneg : s m < 0 := lt_of_not_ge hnot
  let gap : ι → ℝ := fun i => w i * (max (s i) 0 - s i)
  have hgap (i : ι) : 0 ≤ gap i := mul_nonneg (hw.1 i) (sub_nonneg.mpr (le_max_left _ _))
  have hstrict : 0 < gap m := by
    dsimp only [gap]
    rw [max_eq_right hneg.le]
    exact mul_pos hwm (by linarith)
  have hsum := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hgap i) (Finset.mem_univ m)
  have hsumEq : (∑ i, gap i) = inner ℝ w (positiveScores s) - inner ℝ w s := by
    simp only [gap, PiLp.inner_apply, Real.inner_apply, positiveScores,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsumEq, hattain] at hsum
  have hupper : inner ℝ w (positiveScores s) ≤ ‖positiveScores s‖ := by
    calc
      _ ≤ ‖w‖ * ‖positiveScores s‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖positiveScores s‖ := mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)
      _ = _ := one_mul _
  linarith

theorem active_coupled_weight_score_nonneg {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights)
    (hweight : weightedCoupledFunction w x = coupledFunction x) (m : Fin M) (hwm : 0 < w m) :
    0 ≤ coupledScore x m := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  change (2 / (N : ℝ)) * (inner ℝ w (coupledScores x) - _) =
    (2 / (N : ℝ)) * (‖positiveScores (coupledScores x)‖ - _) at hweight
  have hh := mul_left_cancel₀ (ne_of_gt (by positivity : 0 < 2 / (N : ℝ))) hweight
  have hinner : inner ℝ w (coupledScores x) = ‖positiveScores (coupledScores x)‖ := by linarith
  exact active_score_weight_nonneg (coupledScores x) w hw hinner m hwm

theorem weightedCoupledFunction_active_iff {M N : ℕ} (hN : 0 < N)
    (x : ChainSpace M N) (w : EuclideanSpace ℝ (Fin M)) :
    weightedCoupledFunction w x = coupledFunction x ↔
      inner ℝ w (coupledScores x) = ‖positiveCoupledScores x‖ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  change (2 / (N : ℝ)) * (inner ℝ w (coupledScores x) - _) =
    (2 / (N : ℝ)) * (‖positiveCoupledScores x‖ - _) ↔ _
  constructor
  · intro h
    have hh := mul_left_cancel₀ (ne_of_gt (by positivity : 0 < 2 / (N : ℝ))) h
    linarith
  · intro h
    rw [h]

def activeCoupledWeights {M N : ℕ} (x : ChainSpace M N) : Set (EuclideanSpace ℝ (Fin M)) :=
  {w | w ∈ scoreWeights ∧ inner ℝ w (coupledScores x) = ‖positiveCoupledScores x‖}

/-- The literal union-over-active-weights form of the complete raw
subdifferential characterization. `mem_coupledBlockSubgradients_iff`
expands each member into exactly the manuscript's block equation. -/
theorem subdifferential_coupledFunction_blockwise {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    subdifferential coupledFunction x =
      convexHull ℝ (⋃ w ∈ activeCoupledWeights x, coupledBlockSubgradients w x) := by
  rw [subdifferential_coupledFunction_eq_regrouped hN]
  congr 1
  ext g
  simp only [regroupedCoupledGradients, Set.mem_setOf_eq, Set.mem_iUnion,
    activeCoupledWeights, weightedCoupledFunction_active_iff hN]
  constructor
  · rintro ⟨w, hw, hactive, hg⟩
    exact ⟨w, ⟨hw, hactive⟩, hg⟩
  · rintro ⟨w, ⟨hw, hactive⟩, hg⟩
    exact ⟨w, hw, hactive, hg⟩

end WC
