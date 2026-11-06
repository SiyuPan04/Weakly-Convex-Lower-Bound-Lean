import WC.TerminalActivation
import WC.SubgradientCalculus
import WC.Oracle
import WC.ScoreWeightSpace
import WC.CompactMaximumRule

/-! Smooth facet branches of the actual coupled maximum. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

abbrev FanFacet (N : ℕ) := Option (Fin N)

def affineFacet (N K m : ℕ) (a : FanFacet N) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  match a with
  | none => 0
  | some n => tiltIntercept K (m * N + n.val) - (N : ℝ) / 8 * x n

def affineFacetGradient (N : ℕ) (a : FanFacet N) : EuclideanSpace ℝ (Fin N) :=
  match a with
  | none => 0
  | some n => EuclideanSpace.single n (-(N : ℝ) / 8)

theorem affineFacet_le_tiltedBlock (N K m : ℕ) (a : FanFacet N)
    (x : EuclideanSpace ℝ (Fin N)) : affineFacet N K m a x ≤ euclideanTiltedBlock N K m x := by
  cases a with
  | none => exact tiltedBlock_nonneg N K m _
  | some n => exact fanPiece_le_tiltedBlock N K m (fun i => x i) n

theorem affineFacet_attains_tiltedBlock (N K m : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    ∃ a : FanFacet N, affineFacet N K m a x = euclideanTiltedBlock N K m x := by
  obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup'
    (s := insert (0 : ℝ) (Finset.univ.image (fanPiece N K m (fun i => x i))))
    (Finset.insert_nonempty _ _) id
  rcases Finset.mem_insert.mp hb with hb | hb
  · exact ⟨none, (show euclideanTiltedBlock N K m x = 0 from heq.trans hb).symm⟩
  · obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hb
    exact ⟨some n, (show euclideanTiltedBlock N K m x = fanPiece N K m (fun i => x i) n from
      heq.trans hn.symm).symm⟩

theorem hasFDerivAt_affineFacet (N K m : ℕ) (a : FanFacet N)
    (x : EuclideanSpace ℝ (Fin N)) :
    HasFDerivAt (affineFacet N K m a) (innerSL ℝ (affineFacetGradient N a)) x := by
  cases a with
  | none =>
    convert hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x using 1 <;>
      first | rfl | simp [affineFacetGradient]
  | some n =>
    let pr : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) n
    have hp : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin N) => y n) pr x := pr.hasFDerivAt
    have h := (hp.const_mul ((N : ℝ) / 8)).const_sub
      (tiltIntercept K (m * N + n.val))
    convert h using 1
    all_goals try rfl
    ext y
    simp [affineFacetGradient, PiLp.inner_apply, PiLp.proj_apply, smul_eq_mul, pr]
    ring

theorem subdifferential_affineFacet (N K m : ℕ) (a : FanFacet N)
    (x : EuclideanSpace ℝ (Fin N)) :
    subdifferential (affineFacet N K m a) x = {affineFacetGradient N a} := by
  have hg : HasGradientAt (affineFacet N K m a) (affineFacetGradient N a) x :=
    hasGradientAt_iff_hasFDerivAt.mpr (hasFDerivAt_affineFacet N K m a x)
  ext v
  exact frechetSubgradient_iff_gradient hg

def coupledFacetBranch {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) : ℝ :=
  (2 / (N : ℝ)) * (initialWeight w + ∑ m,
    (w m * (affineFacet N (M * N) m.val (a m) (euclideanBlock x m) - 5 / 4) +
      smoothBlockTerm (nextWeight w m) (euclideanBlock x m)))

theorem coupledFacetBranch_le_weightedCoupledFunction {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) : coupledFacetBranch w a x ≤ weightedCoupledFunction w x := by
  rw [weightedCoupledFunction_grouped]
  unfold coupledFacetBranch
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro m _
  refine add_le_add ?_ le_rfl
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right (affineFacet_le_tiltedBlock N (M * N) m.val (a m) (euclideanBlock x m)) _) (hw.1 m)

theorem coupledFacetBranch_attains_weightedCoupledFunction {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (x : ChainSpace M N) :
    ∃ a : Fin M → FanFacet N, coupledFacetBranch w a x = weightedCoupledFunction w x := by
  choose a ha using fun m : Fin M => affineFacet_attains_tiltedBlock N (M * N) m.val (euclideanBlock x m)
  refine ⟨a, ?_⟩
  rw [weightedCoupledFunction_grouped]
  unfold coupledFacetBranch
  simp only [ha]
  rfl

theorem coupledFacetBranch_le_coupledFunction {M N : ℕ}
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) : coupledFacetBranch w a x ≤ coupledFunction x :=
  (coupledFacetBranch_le_weightedCoupledFunction w hw a x).trans (weightedCoupledFunction_le w x hw)

theorem coupledFacetBranch_attains_coupledFunction {M N : ℕ} (x : ChainSpace M N) :
    ∃ (w : EuclideanSpace ℝ (Fin M)) (_ : w ∈ scoreWeights) (a : Fin M → FanFacet N),
      coupledFacetBranch w a x = coupledFunction x := by
  let w := positiveScoreOptimizer (coupledScores x)
  obtain ⟨a, ha⟩ := coupledFacetBranch_attains_weightedCoupledFunction w x
  exact ⟨w, positiveScoreOptimizer_mem _, a, ha.trans (weightedCoupledFunction_attains x)⟩

theorem convexOn_affineFacet (N K m : ℕ) (a : FanFacet N) :
    ConvexOn ℝ Set.univ (affineFacet N K m a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t _ _ hst
  cases a with
  | none => simp [affineFacet]
  | some n =>
    have hc : (s + t) * tiltIntercept K (m * N + n.val) = tiltIntercept K (m * N + n.val) := by
      rw [hst, one_mul]
    simp only [affineFacet, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith

theorem affineFacetGradient_norm_le (N : ℕ) (a : FanFacet N) :
    ‖affineFacetGradient N a‖ ≤ (N : ℝ) / 8 := by
  cases a with
  | none => simp [affineFacetGradient]; positivity
  | some n => simp [affineFacetGradient]

def blockProjection {M N : ℕ} (m : Fin M) : ChainSpace M N →L[ℝ] EuclideanSpace ℝ (Fin N) where
  toFun := fun x => euclideanBlock x m
  map_add' := by intro x y; apply PiLp.ext; intro n; rfl
  map_smul' := by intro c x; apply PiLp.ext; intro n; rfl
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun n => PiLp.continuous_apply 2 _ (m, n))

def embedBlockGradient {M N : ℕ} (m : Fin M) (g : EuclideanSpace ℝ (Fin N)) : ChainSpace M N :=
  WithLp.toLp 2 (fun i => if i.1 = m then g i.2 else 0)

theorem embedBlockGradient_norm {M N : ℕ} (m : Fin M) (g : EuclideanSpace ℝ (Fin N)) :
    ‖embedBlockGradient m g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, embedBlockGradient,
    Fintype.sum_prod_type]
  simp

theorem hasFDerivAt_comp_euclideanBlock {M N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ}
    {g : EuclideanSpace ℝ (Fin N)} (x : ChainSpace M N) (m : Fin M)
    (hf : HasFDerivAt f (innerSL ℝ g) (euclideanBlock x m)) :
    HasFDerivAt (fun y : ChainSpace M N => f (euclideanBlock y m))
      (innerSL ℝ (embedBlockGradient m g)) x := by
  have hp : HasFDerivAt (fun y : ChainSpace M N => euclideanBlock y m) (blockProjection m) x :=
    (blockProjection m).hasFDerivAt
  have h := hf.comp x hp
  convert h using 1
  all_goals try rfl
  ext y
  simp [PiLp.inner_apply, embedBlockGradient, blockProjection,
    euclideanBlock, coupledBlock, Fintype.sum_prod_type]

def blockFacetGradient {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (a : Fin M → FanFacet N)
    (m : Fin M) (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  w m • affineFacetGradient N (a m) + smoothBlockGradient (nextWeight w m) x

theorem hasFDerivAt_blockFacetTerm {M N : ℕ} (hN : 0 < N) (w : EuclideanSpace ℝ (Fin M))
    (a : Fin M → FanFacet N) (m : Fin M) (x : EuclideanSpace ℝ (Fin N)) :
    HasFDerivAt (fun y => w m * (affineFacet N (M * N) m.val (a m) y - 5 / 4) +
      smoothBlockTerm (nextWeight w m) y) (innerSL ℝ (blockFacetGradient w a m x)) x := by
  have hf := ((hasFDerivAt_affineFacet N (M * N) m.val (a m) x).sub_const (5 / 4 : ℝ)).const_mul (w m)
  have h := hf.add (hasFDerivAt_smoothBlockTerm hN (nextWeight w m) x)
  convert h using 1
  all_goals try rfl
  ext y
  simp [blockFacetGradient, smul_eq_mul]

def coupledFacetBranchGradient {M N : ℕ} (w : EuclideanSpace ℝ (Fin M)) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) : ChainSpace M N :=
  (2 / (N : ℝ)) • ∑ m, embedBlockGradient m (blockFacetGradient w a m (euclideanBlock x m))

theorem hasFDerivAt_coupledFacetBranch {M N : ℕ} (hN : 0 < N) (w : EuclideanSpace ℝ (Fin M))
    (a : Fin M → FanFacet N) (x : ChainSpace M N) :
    HasFDerivAt (coupledFacetBranch w a) (innerSL ℝ (coupledFacetBranchGradient w a x)) x := by
  have hterms (m : Fin M) := hasFDerivAt_comp_euclideanBlock x m (hasFDerivAt_blockFacetTerm hN w a m (euclideanBlock x m))
  have h := ((HasFDerivAt.fun_sum (u := Finset.univ) (fun m _ => hterms m)).const_add
    (initialWeight w)).const_mul (2 / (N : ℝ))
  convert h using 1
  all_goals try rfl
  ext y
  simp [coupledFacetBranchGradient, smul_eq_mul, Finset.mul_sum]

theorem weaklyConvex_coupledFacetBranch {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N) :
    WeaklyConvex (9 / 2 : ℝ) (coupledFacetBranch w a) := by
  let f (m : Fin M) (u : EuclideanSpace ℝ (Fin N)) : ℝ :=
    smoothBlockTerm (nextWeight w m) u + w m * (affineFacet N (M * N) m.val (a m) u - 5 / 4)
  have hf (m : Fin M) : WeaklyConvex (9 * (N : ℝ) / 4) (f m) := by
    apply weaklyConvex_add_convex_fn
      (weaklyConvex_smoothBlockTerm hN (nextWeight_nonneg hw m) (nextWeight_le_one hw m))
    have h := ConvexOn.smul (hw.1 m) ((convexOn_affineFacet N (M * N) m.val (a m)).add_const (-(5 / 4 : ℝ)))
    convert h using 1 <;> rfl
  have hs := weaklyConvex_blockSum f hf
  have hc := weaklyConvex_add_const_fn hs (initialWeight w)
  have hscaled := weaklyConvex_const_mul_fn (show 0 ≤ 2 / (N : ℝ) by positivity) hc
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : (2 / (N : ℝ)) * (9 * (N : ℝ) / 4) = 9 / 2 := by field_simp; norm_num
  rw [hL] at hscaled
  convert hscaled using 1
  funext x
  simp only [coupledFacetBranch, f, Finset.sum_add_distrib]
  ring

theorem smoothBlockGradient_norm_le {N : ℕ} {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖smoothBlockGradient ω x‖ ≤ 3 * Real.sqrt (N : ℝ) / 4 := by
  unfold smoothBlockGradient
  rw [norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul (smoothBlockCoefficient_abs_le hω0 hω1 (euclideanProgress x))
    (progressGradient_norm_le x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1 <;> first | rfl | ring

theorem blockFacetGradient_norm_le {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N) (m : Fin M)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖blockFacetGradient w a m x‖ ≤ (N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4 := by
  unfold blockFacetGradient
  calc
    _ ≤ ‖w m • affineFacetGradient N (a m)‖ + ‖smoothBlockGradient (nextWeight w m) x‖ := norm_add_le _ _
    _ ≤ (N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4 := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw.1 m)]
        have h := mul_le_mul (scoreWeights_coord_le_one hw m) (affineFacetGradient_norm_le N (a m))
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using h
      · exact smoothBlockGradient_norm_le (nextWeight_nonneg hw m) (nextWeight_le_one hw m) x

def facetBranchLipschitzConstant (M N : ℕ) : ℝ :=
  (2 / (N : ℝ)) * ((M : ℝ) * ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4))

theorem facetBranchLipschitzConstant_nonneg (M N : ℕ) : 0 ≤ facetBranchLipschitzConstant M N := by
  unfold facetBranchLipschitzConstant
  positivity

theorem coupledFacetBranchGradient_norm_le {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N) (x : ChainSpace M N) :
    ‖coupledFacetBranchGradient w a x‖ ≤ facetBranchLipschitzConstant M N := by
  unfold coupledFacetBranchGradient facetBranchLipschitzConstant
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 2 / (N : ℝ) by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ m, ‖embedBlockGradient m (blockFacetGradient w a m (euclideanBlock x m))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin M, ((N : ℝ) / 8 + 3 * Real.sqrt (N : ℝ) / 4) := by
      apply Finset.sum_le_sum
      intro m _
      rw [embedBlockGradient_norm]
      exact blockFacetGradient_norm_le w hw a m _
    _ = _ := by simp; ring

theorem coupledFacetBranch_lipschitz {M N : ℕ} (hN : 0 < N) (w : EuclideanSpace ℝ (Fin M))
    (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N) :
    GloballyLipschitz (facetBranchLipschitzConstant M N) (coupledFacetBranch w a) := by
  have hd (x : ChainSpace M N) := hasFDerivAt_coupledFacetBranch hN w a x
  have hb (x : ChainSpace M N) : ‖fderiv ℝ (coupledFacetBranch w a) x‖ ≤ facetBranchLipschitzConstant M N := by
    rw [(hd x).fderiv, innerSL_apply_norm]
    exact coupledFacetBranchGradient_norm_le w hw a x
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (hd z).differentiableAt)
    (fun z (_ : z ∈ Set.univ) => hb z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem continuous_initialWeight (M : ℕ) : Continuous (initialWeight (M := M)) := by
  unfold initialWeight
  split_ifs
  · exact PiLp.continuous_apply 2 _ _
  · exact continuous_const

theorem continuous_nextWeight {M : ℕ} (m : Fin M) :
    Continuous (fun w : EuclideanSpace ℝ (Fin M) => nextWeight w m) := by
  unfold nextWeight
  split_ifs
  · exact PiLp.continuous_apply 2 _ _
  · exact continuous_const

theorem continuous_euclideanProgress {N : ℕ} (hN : 0 < N) :
    Continuous (euclideanProgress (N := N)) :=
  continuous_iff_continuousAt.mpr fun x => (hasGradientAt_euclideanProgress hN x).continuousAt

theorem continuous_relayProgress : Continuous relayProgress :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_relayProgress s).continuousAt

theorem continuous_affineFacet (N K m : ℕ) (a : FanFacet N) :
    Continuous (affineFacet N K m a) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_affineFacet N K m a x).continuousAt

theorem coupledFacetBranch_joint_continuous {M N : ℕ} (hN : 0 < N) (a : Fin M → FanFacet N) :
    Continuous (fun p : EuclideanSpace ℝ (Fin M) × ChainSpace M N => coupledFacetBranch p.1 a p.2) := by
  have hψ (m : Fin M) : Continuous (fun p : EuclideanSpace ℝ (Fin M) × ChainSpace M N =>
      euclideanProgress (euclideanBlock p.2 m)) :=
    (continuous_euclideanProgress hN).comp ((blockProjection m).continuous.comp continuous_snd)
  have hf (m : Fin M) : Continuous (fun p : EuclideanSpace ℝ (Fin M) × ChainSpace M N =>
      affineFacet N (M * N) m.val (a m) (euclideanBlock p.2 m)) :=
    (continuous_affineFacet N (M * N) m.val (a m)).comp ((blockProjection m).continuous.comp continuous_snd)
  have hterm (m : Fin M) : Continuous (fun p : EuclideanSpace ℝ (Fin M) × ChainSpace M N =>
      p.1 m * (affineFacet N (M * N) m.val (a m) (euclideanBlock p.2 m) - 5 / 4) +
      smoothBlockTerm (nextWeight p.1 m) (euclideanBlock p.2 m)) := by
    unfold smoothBlockTerm
    exact (((PiLp.continuous_apply 2 _ m).comp continuous_fst).mul ((hf m).sub continuous_const)).add
      ((((continuous_nextWeight m).comp continuous_fst).mul (continuous_relayProgress.comp (hψ m))).sub
        (continuous_const.mul (hψ m)))
  unfold coupledFacetBranch
  exact continuous_const.mul (((continuous_initialWeight M).comp continuous_fst).add
    (continuous_finsetSum Finset.univ (fun m _ => hterm m)))

abbrev FacetTuples (M N : ℕ) := Fin M → FanFacet N

instance facetTupleMetricSpace (M N : ℕ) : MetricSpace (FacetTuples M N) :=
  MetricSpace.induced (fun a => (((Fintype.equivFin (FacetTuples M N)) a).val : ℝ)) (by
    intro a b hab
    apply (Fintype.equivFin (FacetTuples M N)).injective
    apply Fin.ext
    apply Nat.cast_injective (R := ℝ)
    exact hab) inferInstance

instance facetTuple_discreteTopology (M N : ℕ) : DiscreteTopology (FacetTuples M N) := by infer_instance
instance facetTuple_compactSpace (M N : ℕ) : CompactSpace (FacetTuples M N) := by infer_instance

abbrev CoupledBranchParameter (M N : ℕ) := ScoreWeightSpace M × FacetTuples M N

def parameterizedCoupledBranch {M N : ℕ} (p : CoupledBranchParameter M N) : ChainSpace M N → ℝ :=
  coupledFacetBranch p.1.val p.2

theorem parameterizedCoupledBranch_joint_continuous {M N : ℕ} (hN : 0 < N) :
    Continuous (fun p : CoupledBranchParameter M N × ChainSpace M N => parameterizedCoupledBranch p.1 p.2) := by
  have hfinite : Continuous (fun p : FacetTuples M N × (ScoreWeightSpace M × ChainSpace M N) =>
      coupledFacetBranch p.2.1.val p.1 p.2.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro a
    exact (coupledFacetBranch_joint_continuous hN a).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  exact hfinite.comp ((continuous_snd.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

theorem compactMaximum_parameterizedCoupledBranch {M N : ℕ} :
    compactMaximum (parameterizedCoupledBranch (M := M) (N := N)) = coupledFunction := by
  funext x
  have hg : IsGreatest (Set.range (fun p : CoupledBranchParameter M N => parameterizedCoupledBranch p x))
      (coupledFunction x) := by
    constructor
    · obtain ⟨w, hw, a, ha⟩ := coupledFacetBranch_attains_coupledFunction x
      exact ⟨(⟨w, hw⟩, a), ha⟩
    · rintro _ ⟨p, rfl⟩
      exact coupledFacetBranch_le_coupledFunction p.1.val p.1.property p.2 x
  exact hg.csSup_eq

def coupledActiveGradients {M N : ℕ} (x : ChainSpace M N) : Set (ChainSpace M N) :=
  {v | ∃ (w : EuclideanSpace ℝ (Fin M)) (_ : w ∈ scoreWeights) (a : FacetTuples M N),
    coupledFacetBranch w a x = coupledFunction x ∧ v = coupledFacetBranchGradient w a x}

theorem subdifferential_coupledFacetBranch {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (a : Fin M → FanFacet N) (x : ChainSpace M N) :
    subdifferential (coupledFacetBranch w a) x = {coupledFacetBranchGradient w a x} := by
  have hg : HasGradientAt (coupledFacetBranch w a) (coupledFacetBranchGradient w a x) x :=
    hasGradientAt_iff_hasFDerivAt.mpr (hasFDerivAt_coupledFacetBranch hN w a x)
  ext v
  exact frechetSubgradient_iff_gradient hg

theorem activeSlopes_parameterizedCoupledBranch {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    activeSlopes parameterizedCoupledBranch x = coupledActiveGradients x := by
  ext v
  constructor
  · rintro ⟨p, hp, hv⟩
    change coupledFacetBranch p.1.val p.2 x = compactMaximum parameterizedCoupledBranch x at hp
    rw [compactMaximum_parameterizedCoupledBranch] at hp
    change v ∈ subdifferential (coupledFacetBranch p.1.val p.2) x at hv
    rw [subdifferential_coupledFacetBranch hN] at hv
    exact ⟨p.1.val, p.1.property, p.2, hp, hv⟩
  · rintro ⟨w, hw, a, ha, hv⟩
    refine ⟨(⟨w, hw⟩, a), ?_, ?_⟩
    · change coupledFacetBranch w a x = compactMaximum parameterizedCoupledBranch x
      rw [compactMaximum_parameterizedCoupledBranch]
      exact ha
    · change v ∈ subdifferential (coupledFacetBranch w a) x
      rw [subdifferential_coupledFacetBranch hN]
      exact hv

/-- A complete, actual subdifferential formula for the coupled function. -/
theorem subdifferential_coupledFunction_eq_convexHull {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    subdifferential coupledFunction x = convexHull ℝ (coupledActiveGradients x) := by
  have h := subdifferential_compactMaximum_eq_convexHull
    (facetBranchLipschitzConstant_nonneg M N) (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (parameterizedCoupledBranch_joint_continuous hN)
    (fun p : CoupledBranchParameter M N => coupledFacetBranch_lipschitz hN p.1.val p.1.property p.2)
    (fun p : CoupledBranchParameter M N => weaklyConvex_coupledFacetBranch hN p.1.val p.1.property p.2) x
  rw [compactMaximum_parameterizedCoupledBranch, activeSlopes_parameterizedCoupledBranch hN] at h
  exact h

end WC
