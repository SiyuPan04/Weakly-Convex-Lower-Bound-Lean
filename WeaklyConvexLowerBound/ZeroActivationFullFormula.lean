import WeaklyConvexLowerBound.FullSubdiffCharacterization
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The zero-activation full-formula problem

This module isolates structural facts needed for the remaining direction of
the full-subdifferential formula at `activationNorm z = 0`.  In particular,
the apparent union over active outer weights is already convex: the product
`w m * u m` is a perspective of the convex tilted-fan subdifferential.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set
open scoped BigOperators Topology

/-! ## Convex combinations of the elementary parameters -/

theorem feasibleOuterWeight_combo {M : Nat} {w v : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (hv : FeasibleOuterWeight v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    FeasibleOuterWeight (a • w + b • v) := by
  constructor
  · intro m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hw.1 m, hv.1 m]
  · have hpoint (m : Fin M) :
        (a * w m + b * v m) ^ 2 ≤ a * (w m) ^ 2 + b * (v m) ^ 2 := by
      have hs : 0 ≤ a * b * (w m - v m) ^ 2 :=
        mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
      nlinarith
    calc
      (∑ m, ((a • w + b • v) m) ^ 2) =
          ∑ m, (a * w m + b * v m) ^ 2 := by
            apply Finset.sum_congr rfl
            intro m _
            simp
      _ ≤ ∑ m, (a * (w m) ^ 2 + b * (v m) ^ 2) :=
        Finset.sum_le_sum fun m _ => hpoint m
      _ = a * (∑ m, (w m) ^ 2) + b * (∑ m, (v m) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 1 := by nlinarith [hw.2, hv.2]

theorem outerDot_combo_left {M : Nat} (w v s : Fin M → ℝ)
    (a b : ℝ) :
    outerDot (a • w + b • v) s =
      a * outerDot w s + b * outerDot v s := by
  unfold outerDot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem activeOuterWeight_combo {M N : Nat} {z : BlockVec M N}
    {w v : Fin M → ℝ} (hw : ActiveOuterWeight z w)
    (hv : ActiveOuterWeight z v) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ActiveOuterWeight z (a • w + b • v) := by
  constructor
  · exact feasibleOuterWeight_combo hw.1 hv.1 ha hb hab
  · rw [outerDot_combo_left, hw.2, hv.2, ← add_mul, hab, one_mul]

theorem phiSubgradient_combo {N : Nat} {x u v : Fin N → ℝ}
    (hu : PhiSubgradient x u) (hv : PhiSubgradient x v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    PhiSubgradient x (a • u + b • v) := by
  obtain ⟨wu, hwu0, hwusum, hwuactive, hucoord⟩ := hu
  obtain ⟨wv, hwv0, hwvsum, hwvactive, hvcoord⟩ := hv
  let weights : FacetIndex N → ℝ := fun s => a * wu s + b * wv s
  refine ⟨weights, ?_, ?_, ?_, ?_⟩
  · intro s
    dsimp [weights]
    nlinarith [mul_nonneg ha (hwu0 s), mul_nonneg hb (hwv0 s)]
  · dsimp [weights]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hwusum, hwvsum, mul_one, mul_one, hab]
  · intro s hs
    by_cases hus : wu s = 0
    · have hvs : wv s ≠ 0 := by
        intro hvs
        apply hs
        simp [weights, hus, hvs]
      exact hwvactive s hvs
    · exact hwuactive s hus
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hucoord, hvcoord]
    dsimp [weights]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring

theorem nextOuterWeight_combo {M : Nat} (w v : Fin M → ℝ)
    (m : Fin M) (a b : ℝ) :
    nextOuterWeight (a • w + b • v) m =
      a * nextOuterWeight w m + b * nextOuterWeight v m := by
  unfold nextOuterWeight
  split <;> simp

/-! ## Convexity of the displayed formula set -/

theorem hardFormulaSet_convex {M N : Nat} (z : BlockVec M N) :
    Convex ℝ (hardFormulaSet z) := by
  intro g hg h hh a b ha hb hab
  let rg : GeneralHardFormulaReply z g := Classical.choice hg
  let rh : GeneralHardFormulaReply z h := Classical.choice hh
  let w : Fin M → ℝ := a • rg.w + b • rh.w
  have hwactive : ActiveOuterWeight z w :=
    activeOuterWeight_combo rg.active rh.active ha hb hab
  let u : BlockVec M N := fun m =>
    if hwm : w m = 0 then rg.u m
    else
      (a * rg.w m / w m) • rg.u m +
        (b * rh.w m / w m) • rh.u m
  have hwm_nonneg (m : Fin M) : 0 ≤ w m := hwactive.1.1 m
  have hleft_nonneg (m : Fin M) : 0 ≤ a * rg.w m :=
    mul_nonneg ha (rg.active.1.1 m)
  have hright_nonneg (m : Fin M) : 0 ≤ b * rh.w m :=
    mul_nonneg hb (rh.active.1.1 m)
  have hwcoord (m : Fin M) :
      w m = a * rg.w m + b * rh.w m := by
    simp [w]
  have hu : ∀ m, PhiSubgradient (z m) (u m) := by
    intro m
    by_cases hwm : w m = 0
    · simpa [u, hwm] using rg.u_subgradient m
    · have hwpos : 0 < w m := lt_of_le_of_ne (hwm_nonneg m) (Ne.symm hwm)
      have hca : 0 ≤ a * rg.w m / w m := div_nonneg (hleft_nonneg m) hwpos.le
      have hcb : 0 ≤ b * rh.w m / w m := div_nonneg (hright_nonneg m) hwpos.le
      have hsum : a * rg.w m / w m + b * rh.w m / w m = 1 := by
        rw [← add_div, ← hwcoord]
        exact div_self hwm
      simpa [u, hwm] using
        phiSubgradient_combo (rg.u_subgradient m) (rh.u_subgradient m)
          hca hcb hsum
  refine ⟨⟨w, hwactive, u, hu, ?_⟩⟩
  intro m j
  have hnext := nextOuterWeight_combo rg.w rh.w m a b
  have hprogress :
      1 - nextOuterWeight w m =
        a * (1 - nextOuterWeight rg.w m) +
          b * (1 - nextOuterWeight rh.w m) := by
    dsimp [w]
    rw [hnext]
    nlinarith
  have hproduct :
      w m * u m j =
        a * (rg.w m * rg.u m j) +
          b * (rh.w m * rh.u m j) := by
    by_cases hwm : w m = 0
    · have hla : a * rg.w m = 0 := by
        nlinarith [hleft_nonneg m, hright_nonneg m, hwcoord m]
      have hlb : b * rh.w m = 0 := by
        nlinarith [hleft_nonneg m, hright_nonneg m, hwcoord m]
      rw [hwm, zero_mul, ← mul_assoc, hla, zero_mul,
        ← mul_assoc, hlb, zero_mul, add_zero]
    · simp only [u, dif_neg hwm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hwm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rg.g_eq, rh.g_eq]
  rw [hproduct, hprogress]
  ring

theorem convexHull_hardFormulaSet_eq {M N : Nat} (z : BlockVec M N) :
    convexHull ℝ (hardFormulaSet z) = hardFormulaSet z := by
  exact convexHull_eq_self.2 (hardFormulaSet_convex z)

/-! ## Compactness of the displayed formula set -/

def activeOuterWeightSet {M N : Nat} (z : BlockVec M N) :
    Set (Fin M → ℝ) :=
  {w | ActiveOuterWeight z w}

theorem activeOuterWeightSet_isClosed {M N : Nat} (z : BlockVec M N) :
    IsClosed (activeOuterWeightSet z) := by
  change IsClosed
    ({w : Fin M → ℝ | ∀ m, 0 ≤ w m} ∩
      {w : Fin M → ℝ | (∑ m, (w m) ^ 2) ≤ 1} ∩
      {w : Fin M → ℝ |
        outerDot w (fun m => sigmaScore z m) = activationNorm z})
  have hnonneg : IsClosed {w : Fin M → ℝ | ∀ m, 0 ≤ w m} := by
    rw [show {w : Fin M → ℝ | ∀ m, 0 ≤ w m} =
        ⋂ m, {w : Fin M → ℝ | 0 ≤ w m} by ext w; simp]
    exact isClosed_iInter fun m =>
      isClosed_le continuous_const (continuous_apply m)
  have hsumContinuous :
      Continuous (fun w : Fin M → ℝ => ∑ m, (w m) ^ 2) := by
    fun_prop
  have hsum : IsClosed {w : Fin M → ℝ | (∑ m, (w m) ^ 2) ≤ 1} :=
    isClosed_le hsumContinuous continuous_const
  have hdotContinuous : Continuous
      (fun w : Fin M → ℝ => outerDot w (fun m => sigmaScore z m)) := by
    unfold outerDot
    fun_prop
  have hdot : IsClosed {w : Fin M → ℝ |
      outerDot w (fun m => sigmaScore z m) = activationNorm z} :=
    isClosed_eq hdotContinuous continuous_const
  exact (hnonneg.inter hsum).inter hdot

theorem activeOuterWeightSet_isCompact {M N : Nat} (z : BlockVec M N) :
    IsCompact (activeOuterWeightSet z) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : Fin M → ℝ) 1))
    (activeOuterWeightSet_isClosed z)
  intro w hw
  exact ⟨hw.1.1, fun m => feasibleOuterWeight_le_one hw.1 m⟩

def phiSubgradientSet {N : Nat} (x : Fin N → ℝ) :
    Set (Fin N → ℝ) :=
  {u | PhiSubgradient x u}

theorem phiSubgradientSet_isClosed {N : Nat} (hN : 0 < N)
    (x : Fin N → ℝ) : IsClosed (phiSubgradientSet x) := by
  have heq : phiSubgradientSet x =
      ⋂ y : Fin N → ℝ,
        {u : Fin N → ℝ | phi x + vecDot u (y - x) ≤ phi y} := by
    ext u
    simp only [phiSubgradientSet, Set.mem_setOf_eq, Set.mem_iInter]
    exact phiSubgradient_iff_vecConvexSubgradient hN x u
  rw [heq]
  apply isClosed_iInter
  intro y
  apply isClosed_le
  · unfold vecDot
    fun_prop
  · exact continuous_const

theorem phiSubgradientSet_subset_convexHull_range_facetSlope {N : Nat}
    (x : Fin N → ℝ) :
    phiSubgradientSet x ⊆ convexHull ℝ (Set.range (@facetSlope N)) := by
  intro u hu
  obtain ⟨weights, hweights0, hweightssum, _hactive, hucoord⟩ := hu
  apply mem_convexHull_of_exists_fintype weights (@facetSlope N)
  · exact hweights0
  · exact hweightssum
  · intro s
    exact Set.mem_range_self s
  · funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (hucoord i).symm

theorem phiSubgradientSet_isCompact {N : Nat} (hN : 0 < N)
    (x : Fin N → ℝ) : IsCompact (phiSubgradientSet x) := by
  apply IsCompact.of_isClosed_subset
    (Set.finite_range (@facetSlope N) |>.isCompact_convexHull ℝ)
    (phiSubgradientSet_isClosed hN x)
    (phiSubgradientSet_subset_convexHull_range_facetSlope x)

def hardFormulaParameterSet {M N : Nat} (z : BlockVec M N) :
    Set ((Fin M → ℝ) × BlockVec M N) :=
  activeOuterWeightSet z ×ˢ
    Set.univ.pi (fun m => phiSubgradientSet (z m))

theorem hardFormulaParameterSet_isCompact {M N : Nat}
    (hN : 0 < N) (z : BlockVec M N) :
    IsCompact (hardFormulaParameterSet z) := by
  exact (activeOuterWeightSet_isCompact z).prod
    (isCompact_univ_pi fun m => phiSubgradientSet_isCompact hN (z m))

def hardFormulaParameterMap {M N : Nat} (z : BlockVec M N)
    (p : (Fin M → ℝ) × BlockVec M N) : BlockVec M N :=
  fun m j =>
    (2 / (N : ℝ)) *
      (p.1 m * p.2 m j -
        (1 - nextOuterWeight p.1 m) * psiGrad (z m) j)

theorem continuous_hardFormulaParameterMap {M N : Nat}
    (z : BlockVec M N) : Continuous (hardFormulaParameterMap z) := by
  apply continuous_pi
  intro m
  apply continuous_pi
  intro j
  have hw : Continuous
      (fun p : (Fin M → ℝ) × BlockVec M N => p.1 m) :=
    (continuous_apply m).comp continuous_fst
  have hu : Continuous
      (fun p : (Fin M → ℝ) × BlockVec M N => p.2 m j) :=
    (continuous_apply j).comp ((continuous_apply m).comp continuous_snd)
  have hnext : Continuous
      (fun p : (Fin M → ℝ) × BlockVec M N => nextOuterWeight p.1 m) := by
    unfold nextOuterWeight
    split
    · exact (continuous_apply _).comp continuous_fst
    · exact continuous_const
  change Continuous (fun p : (Fin M → ℝ) × BlockVec M N =>
    (2 / (N : ℝ)) *
      (p.1 m * p.2 m j -
        (1 - nextOuterWeight p.1 m) * psiGrad (z m) j))
  exact continuous_const.mul
    ((hw.mul hu).sub ((continuous_const.sub hnext).mul continuous_const))

theorem hardFormulaSet_eq_parameter_image {M N : Nat}
    (z : BlockVec M N) :
    hardFormulaSet z =
      hardFormulaParameterMap z '' hardFormulaParameterSet z := by
  ext g
  constructor
  · intro hg
    let reply : GeneralHardFormulaReply z g := Classical.choice hg
    refine ⟨(reply.w, reply.u), ?_, ?_⟩
    · exact ⟨reply.active, fun m _ => reply.u_subgradient m⟩
    · funext m j
      exact (reply.g_eq m j).symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨{
      w := p.1
      active := hp.1
      u := p.2
      u_subgradient := fun m => hp.2 m (Set.mem_univ m)
      g_eq := ?_ }⟩
    intro m j
    rfl

theorem hardFormulaSet_isCompact {M N : Nat} (hN : 0 < N)
    (z : BlockVec M N) : IsCompact (hardFormulaSet z) := by
  rw [hardFormulaSet_eq_parameter_image]
  exact (hardFormulaParameterSet_isCompact hN z).image
    (continuous_hardFormulaParameterMap z)

theorem hardFormulaSet_isClosed {M N : Nat} (hN : 0 < N)
    (z : BlockVec M N) : IsClosed (hardFormulaSet z) :=
  (hardFormulaSet_isCompact hN z).isClosed

/-! ## Finite-dimensional separation in the paper's block pairing -/

def blockUnit {M N : Nat} (m : Fin M) (j : Fin N) : BlockVec M N :=
  fun m' j' => if m' = m ∧ j' = j then 1 else 0

theorem blockVec_eq_sum_smul_blockUnit {M N : Nat} (x : BlockVec M N) :
    x = ∑ m, ∑ j, x m j • blockUnit m j := by
  classical
  funext m' j'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockUnit,
    mul_ite, mul_one, mul_zero]
  symm
  rw [Finset.sum_eq_single m']
  · rw [Finset.sum_eq_single j']
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · intro m _ hm
    simp [Ne.symm hm]
  · simp

def strongDualDirection {M N : Nat}
    (L : StrongDual ℝ (BlockVec M N)) : BlockVec M N :=
  fun m j => L (blockUnit m j)

theorem strongDual_apply_eq_blockDot {M N : Nat}
    (L : StrongDual ℝ (BlockVec M N)) (x : BlockVec M N) :
    L x = blockDot x (strongDualDirection L) := by
  classical
  calc
    L x = L (∑ m, ∑ j, x m j • blockUnit m j) :=
      congrArg L (blockVec_eq_sum_smul_blockUnit x)
    _ = ∑ m, ∑ j, x m j * L (blockUnit m j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = blockDot x (strongDualDirection L) := rfl

theorem hardFormulaSet_nonempty_of_activationNorm_eq_zero {M N : Nat}
    {z : BlockVec M N} (hR0 : activationNorm z = 0) :
    (hardFormulaSet z).Nonempty := by
  let u : BlockVec M N := fun m =>
    facetSlope (Classical.choose (exists_activeFacet (z m)))
  let p : (Fin M → ℝ) × BlockVec M N := (0, u)
  have hp : p ∈ hardFormulaParameterSet z := by
    change ActiveOuterWeight z (0 : Fin M → ℝ) ∧
      u ∈ Set.univ.pi (fun m => phiSubgradientSet (z m))
    constructor
    · constructor
      · constructor
        · intro m
          simp
        · simp
      · simp [outerDot, hR0]
    · intro m _
      change PhiSubgradient (z m) (u m)
      exact activeFacet_slope_is_PhiSubgradient (z m)
        (Classical.choose_spec (exists_activeFacet (z m)))
  refine ⟨hardFormulaParameterMap z p, ?_⟩
  rw [hardFormulaSet_eq_parameter_image]
  exact ⟨p, hp, rfl⟩

/-- Once every ambient direction is dominated by one displayed formula
vector, closed-convex separation converts those support inequalities into
membership.  This is the exact finite-dimensional geometric bridge needed
by the zero-activation reverse inclusion. -/
theorem mem_hardFormulaSet_of_directional_domination {M N : Nat}
    (hN : 0 < N) (z g : BlockVec M N)
    (hdom : ∀ d : BlockVec M N,
      ∃ q ∈ hardFormulaSet z, blockDot g d ≤ blockDot q d) :
    g ∈ hardFormulaSet z := by
  by_contra hg
  obtain ⟨L, c, hLc, hcL⟩ := geometric_hahn_banach_closed_point
    (hardFormulaSet_convex z) (hardFormulaSet_isClosed hN z) hg
  obtain ⟨q, hq, hdomq⟩ := hdom (strongDualDirection L)
  have hqL : blockDot q (strongDualDirection L) < c := by
    simpa [← strongDual_apply_eq_blockDot L q] using hLc q hq
  have hLg : c < blockDot g (strongDualDirection L) := by
    simpa [← strongDual_apply_eq_blockDot L g] using hcL
  linarith

/-- The sole remaining analytic statement can be exposed independently of
the separation argument: a semantic full subgradient must be directionally
dominated by one active formula vector. -/
def ZeroActivationDirectionalDomination {M N : Nat}
    (z g : BlockVec M N) : Prop :=
  ∀ d : BlockVec M N,
    ∃ q ∈ hardFormulaSet z, blockDot g d ≤ blockDot q d

theorem fullSubdiff_subset_hardFormulaSet_of_zeroActivationDirectionalDomination
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (_hR0 : activationNorm z = 0)
    (hdir : ∀ g ∈ fullSubdiff 1 (@hardValue M N) z,
      ZeroActivationDirectionalDomination z g) :
    fullSubdiff 1 (@hardValue M N) z ⊆ hardFormulaSet z := by
  intro g hg
  exact mem_hardFormulaSet_of_directional_domination hA.N_pos z g
    (hdir g hg)

theorem fullSubdiff_eq_convexHull_hardFormulaSet_of_zeroActivationDirectionalDomination
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (hR0 : activationNorm z = 0)
    (hdir : ∀ g ∈ fullSubdiff 1 (@hardValue M N) z,
      ZeroActivationDirectionalDomination z g) :
    fullSubdiff 1 (@hardValue M N) z = convexHull ℝ (hardFormulaSet z) := by
  rw [convexHull_hardFormulaSet_eq]
  apply Set.Subset.antisymm
  · exact fullSubdiff_subset_hardFormulaSet_of_zeroActivationDirectionalDomination
      hA hR0 hdir
  · exact hardFormulaSet_subset_fullSubdiff hA z

/-! ## The finite-fan directional model -/

theorem exists_activeFacet_max_vecDot {N : Nat}
    (x d : Fin N → ℝ) :
    ∃ s : FacetIndex N,
      ActiveFacet x s ∧
      ∀ r : FacetIndex N, ActiveFacet x r →
        vecDot (facetSlope r) d ≤ vecDot (facetSlope s) d := by
  classical
  let active : Finset (FacetIndex N) :=
    Finset.univ.filter (fun s => ActiveFacet x s)
  have hactive : active.Nonempty := by
    obtain ⟨s, hs⟩ := exists_activeFacet x
    exact ⟨s, by simp [active, hs]⟩
  obtain ⟨s, hs, hmax⟩ := active.exists_max_image
    (fun r => vecDot (facetSlope r) d) hactive
  refine ⟨s, ?_, ?_⟩
  · simpa [active] using hs
  · intro r hr
    exact hmax r (by simp [active, hr])

theorem facetValue_line {N : Nat} (x d : Fin N → ℝ)
    (s : FacetIndex N) (t : ℝ) :
    facetValue (x + t • d) s =
      facetValue x s + t * vecDot (facetSlope s) d := by
  rw [facetValue_affine x (x + t • d) s]
  have hsub : x + t • d - x = t • d := by
    ext j
    simp
  rw [hsub, vecDot_smul_right_param]

theorem continuous_facetValue_line {N : Nat} (x d : Fin N → ℝ)
    (s : FacetIndex N) :
    Continuous (fun t : ℝ => facetValue (x + t • d) s) := by
  rw [show (fun t : ℝ => facetValue (x + t • d) s) =
      fun t => facetValue x s + t * vecDot (facetSlope s) d by
    funext t
    exact facetValue_line x d s t]
  fun_prop

/-- Along every direction, one active facet realizes the tilted fan on a
short one-sided segment.  Its slope is therefore a genuine
`PhiSubgradient` and gives the exact directional linearization. -/
theorem exists_phiSubgradient_line_exact {N : Nat} (x d : Fin N → ℝ) :
    ∃ u : Fin N → ℝ, PhiSubgradient x u ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
        phi (x + t • d) = phi x + t * vecDot u d := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_activeFacet_max_vecDot x d
  refine ⟨facetSlope s, activeFacet_slope_is_PhiSubgradient x hs, ?_⟩
  have heventually : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ r : FacetIndex N, 0 ≤ t →
        facetValue (x + t • d) r ≤ facetValue (x + t • d) s := by
    apply Filter.eventually_all.2
    intro r
    by_cases hr : ActiveFacet x r
    · filter_upwards [] with t
      intro ht0
      rw [facetValue_line, facetValue_line, hr, hs]
      have hmul := mul_le_mul_of_nonneg_left (hmax r hr) ht0
      linarith
    · have hrlt : facetValue x r < facetValue x s := by
        rw [hs]
        exact lt_of_le_of_ne (facetValue_le_phi x r) hr
      have hrlt0 :
          facetValue (x + (0 : ℝ) • d) r <
            facetValue (x + (0 : ℝ) • d) s := by
        simpa using hrlt
      have hev := (continuous_facetValue_line x d r).continuousAt.eventually_lt
        (continuous_facetValue_line x d s).continuousAt hrlt0
      exact hev.mono fun t ht _ => ht.le
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp heventually
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht0 htδ
  have htδ' : t < δ := by linarith
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact htδ'
  have hall := hball htball
  have hsline : ActiveFacet (x + t • d) s :=
    (activeFacet_iff_maximal (x + t • d) s).2 fun r => hall r ht0
  calc
    phi (x + t • d) = facetValue (x + t • d) s := hsline.symm
    _ = facetValue x s + t * vecDot (facetSlope s) d :=
      facetValue_line x d s t
    _ = phi x + t * vecDot (facetSlope s) d := by rw [hs]

theorem exists_blockPhiSubgradient_line_exact {M N : Nat}
    (z d : BlockVec M N) :
    ∃ u : BlockVec M N, (∀ m, PhiSubgradient (z m) (u m)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
        ∀ m, phi (z m + t • d m) =
          phi (z m) + t * vecDot (u m) (d m) := by
  classical
  have hlocal : ∀ m : Fin M,
      ∃ u : Fin N → ℝ, ∃ ε : ℝ,
        PhiSubgradient (z m) u ∧ 0 < ε ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ ε →
            phi (z m + t • d m) =
              phi (z m) + t * vecDot u (d m) := by
    intro m
    obtain ⟨u, hu, ε, hε, hline⟩ :=
      exists_phiSubgradient_line_exact (z m) (d m)
    exact ⟨u, ε, hu, hε, hline⟩
  choose u ε hu hε hline using hlocal
  refine ⟨u, hu, ?_⟩
  have heventually : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ m : Fin M, 0 ≤ t →
        phi (z m + t • d m) =
          phi (z m) + t * vecDot (u m) (d m) := by
    apply Filter.eventually_all.2
    intro m
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε m)] with t ht
    intro ht0
    apply hline m t ht0
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0] at ht
    exact ht.le
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp heventually
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht0 htδ
  have htδ' : t < δ := by linarith
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact htδ'
  exact fun m => (hball htball) m ht0

def previousLinearRate {M : Nat} (p : Fin M → ℝ) (m : Fin M) : ℝ :=
  if hm : m.1 = 0 then 0 else p ⟨m.1 - 1, by omega⟩

theorem sum_weight_mul_previousLinearRate {M : Nat} (hM : 0 < M)
    (w p : Fin M → ℝ) :
    (∑ m, w m * previousLinearRate p m) =
      ∑ m, nextOuterWeight w m * p m := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [previousLinearRate, nextOuterWeight]
  apply Finset.sum_congr rfl
  intro m _
  congr 2

def blockLinearRate {M N : Nat} (z u d : BlockVec M N)
    (m : Fin M) : ℝ :=
  vecDot (u m) (d m) +
    previousLinearRate (fun k => vecDot (psiGrad (z k)) (d k)) m

def zeroScoreRate {M N : Nat} (z u d : BlockVec M N)
    (m : Fin M) : ℝ :=
  if sigmaScore z m = 0 then blockLinearRate z u d m else 0

theorem canonicalOuterWeight_zeroScoreRate_active {M N : Nat}
    {z u d : BlockVec M N} (hR0 : activationNorm z = 0) :
    ActiveOuterWeight z (canonicalOuterWeight (zeroScoreRate z u d)) := by
  constructor
  · exact canonicalOuterWeight_feasible _
  · rw [hR0]
    unfold outerDot
    apply Finset.sum_eq_zero
    intro m _
    by_cases hs : sigmaScore z m = 0
    · simp [hs]
    · have hr : zeroScoreRate z u d m = 0 := by simp [zeroScoreRate, hs]
      have hw : canonicalOuterWeight (zeroScoreRate z u d) m = 0 := by
        simp [canonicalOuterWeight, hr]
      simp [hw]

theorem outerDot_blockLinearRate_sub {M N : Nat} (hM : 0 < M)
    (z u d : BlockVec M N) (w : Fin M → ℝ) :
    outerDot w (blockLinearRate z u d) -
        (∑ m, vecDot (psiGrad (z m)) (d m)) =
      ∑ m, (w m * vecDot (u m) (d m) -
        netProgressWeight w m * vecDot (psiGrad (z m)) (d m)) := by
  let p : Fin M → ℝ := fun m => vecDot (psiGrad (z m)) (d m)
  have hshift := sum_weight_mul_previousLinearRate hM w p
  unfold outerDot blockLinearRate
  dsimp [p] at hshift ⊢
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hshift]
  unfold netProgressWeight
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

theorem canonicalOuterWeight_zeroScoreRate_dot_blockLinearRate
    {M N : Nat} (z u d : BlockVec M N) :
    outerDot (canonicalOuterWeight (zeroScoreRate z u d))
        (blockLinearRate z u d) =
      positiveNorm (zeroScoreRate z u d) := by
  let w := canonicalOuterWeight (zeroScoreRate z u d)
  have heq : outerDot w (blockLinearRate z u d) =
      outerDot w (zeroScoreRate z u d) := by
    unfold outerDot
    apply Finset.sum_congr rfl
    intro m _
    by_cases hs : sigmaScore z m = 0
    · simp [zeroScoreRate, hs]
    · have hr : zeroScoreRate z u d m = 0 := by simp [zeroScoreRate, hs]
      have hw : w m = 0 := by
        simp [w, canonicalOuterWeight, hr]
      simp [hw]
  rw [heq]
  exact canonicalOuterWeight_dot _

/-! ## Local disappearance of the strictly negative score coordinates -/

theorem continuous_q : Continuous q := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_q t).continuousAt

theorem continuous_psi_line {N : Nat} (x d : Fin N → ℝ) :
    Continuous (fun t : ℝ => psi (x + t • d)) := by
  unfold psi
  apply Continuous.div_const
  apply continuous_finsetSum
  intro j _
  apply continuous_q.comp
  fun_prop

theorem continuous_phi_line {N : Nat} (x d : Fin N → ℝ) :
    Continuous (fun t : ℝ => phi (x + t • d)) := by
  unfold phi
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro s _
  exact continuous_facetValue_line x d s

theorem continuous_previousProgress_line {M N : Nat}
    (z d : BlockVec M N) (m : Fin M) :
    Continuous (fun t : ℝ => previousProgress (z + t • d) m) := by
  unfold previousProgress
  split
  · exact continuous_const
  · simpa only [Pi.add_apply, Pi.smul_apply] using
      continuous_psi_line
        (z ⟨m.1 - 1, by omega⟩) (d ⟨m.1 - 1, by omega⟩)

theorem continuous_sigmaScore_line {M N : Nat}
    (z d : BlockVec M N) (m : Fin M) :
    Continuous (fun t : ℝ => sigmaScore (z + t • d) m) := by
  unfold sigmaScore
  have hphi : Continuous (fun t : ℝ => phi ((z + t • d) m)) := by
    simpa only [Pi.add_apply, Pi.smul_apply] using
      continuous_phi_line (z m) (d m)
  exact (hphi.add (continuous_previousProgress_line z d m)).sub continuous_const

theorem exists_score_negative_stability {M N : Nat}
    (z d : BlockVec M N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      ∀ m, sigmaScore z m < 0 → sigmaScore (z + t • d) m ≤ 0 := by
  have heventually : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ m : Fin M, sigmaScore z m < 0 →
        sigmaScore (z + t • d) m ≤ 0 := by
    apply Filter.eventually_all.2
    intro m
    by_cases hm : sigmaScore z m < 0
    · have hm0 : sigmaScore (z + (0 : ℝ) • d) m < 0 := by
        simpa using hm
      have hev := (continuous_sigmaScore_line z d m).continuousAt.eventually_lt
        continuous_const.continuousAt hm0
      exact hev.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ ht => (hm ht).elim
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp heventually
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht0 htδ
  have htδ' : t < δ := by linarith
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact htδ'
  exact hball htball

theorem exists_blockPhiSubgradient_and_score_stability {M N : Nat}
    (z d : BlockVec M N) :
    ∃ u : BlockVec M N, (∀ m, PhiSubgradient (z m) (u m)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
        (∀ m, phi (z m + t • d m) =
          phi (z m) + t * vecDot (u m) (d m)) ∧
        (∀ m, sigmaScore z m < 0 →
          sigmaScore (z + t • d) m ≤ 0) := by
  obtain ⟨u, hu, εphi, hεphi, hphi⟩ :=
    exists_blockPhiSubgradient_line_exact z d
  obtain ⟨εscore, hεscore, hscore⟩ :=
    exists_score_negative_stability z d
  refine ⟨u, hu, min εphi εscore, lt_min hεphi hεscore, ?_⟩
  intro t ht0 ht
  exact ⟨hphi t ht0 (ht.trans (min_le_left εphi εscore)),
    hscore t ht0 (ht.trans (min_le_right εphi εscore))⟩

theorem canonicalOuterWeight_line_active_at_zero {M N : Nat}
    {z d : BlockVec M N} (hR0 : activationNorm z = 0)
    {t : ℝ}
    (hnegative : ∀ m, sigmaScore z m < 0 →
      sigmaScore (z + t • d) m ≤ 0) :
    ActiveOuterWeight z
      (canonicalOuterWeight (sigmaScore (z + t • d))) := by
  let w := canonicalOuterWeight (sigmaScore (z + t • d))
  constructor
  · exact canonicalOuterWeight_feasible _
  · rw [hR0]
    unfold outerDot
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : sigmaScore z m = 0
    · simp [hm]
    · have hmneg : sigmaScore z m < 0 :=
        lt_of_le_of_ne
          (sigmaScore_nonpos_of_activationNorm_eq_zero hR0 m) hm
      have hym := hnegative m hmneg
      have hw : w m = 0 := by
        simp [w, canonicalOuterWeight, max_eq_right hym]
      change w m * sigmaScore z m = 0
      rw [hw, zero_mul]

/-- A fixed active-facet choice gives a uniform quadratic upper model for
every outer weight that is active at the base point. -/
theorem GeneralHardFormulaReply.activationBranch_line_upper
    {M N : Nat} (hA : Admissible M N) {z g d : BlockVec M N}
    (reply : GeneralHardFormulaReply z g) {t : ℝ} (_ht0 : 0 ≤ t)
    (hphi : ∀ m, phi (z m + t • d m) =
      phi (z m) + t * vecDot (reply.u m) (d m)) :
    activationBranch reply.w (z + t • d) - activationBranch reply.w z ≤
      t * blockDot g d +
        (9 / 8 : ℝ) * t ^ 2 * blockSq d := by
  let y : BlockVec M N := z + t • d
  let a : Fin M → ℝ := netProgressWeight reply.w
  have hfan : branchFanDifference reply.w y z =
      t * ((2 / (N : ℝ)) *
        ∑ m, reply.w m * vecDot (reply.u m) (d m)) := by
    unfold branchFanDifference
    dsimp [y]
    simp_rw [hphi]
    have htermFan (m : Fin M) :
        reply.w m *
            (phi (z m) + t * vecDot (reply.u m) (d m) - phi (z m)) =
          t * (reply.w m * vecDot (reply.u m) (d m)) := by
      ring
    simp_rw [htermFan]
    rw [← Finset.mul_sum]
    ring
  have hyblock (m : Fin M) : y m - z m = t • d m := by
    dsimp [y]
    ext j
    simp
  have hpsi (m : Fin M) :
      t * vecDot (psiGrad (z m)) (d m) -
          (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m) ≤
        psi (y m) - psi (z m) := by
    have h := psi_lower_descent hA.N_pos (z m) (y m)
    rw [hyblock, vecDot_smul_right_param, vecSq_smul_param] at h
    linarith
  have hterm (m : Fin M) :
      a m * (t * vecDot (psiGrad (z m)) (d m) -
          (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m)) ≤
        a m * (psi (y m) - psi (z m)) :=
    mul_le_mul_of_nonneg_left (hpsi m)
      (netProgressWeight_nonneg reply.active.1 m)
  have hsum := Finset.sum_le_sum
    (fun m (_ : m ∈ (Finset.univ : Finset (Fin M))) => hterm m)
  have hremTerm (m : Fin M) :
      a m * ((9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m)) ≤
        (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m) := by
    have ha := netProgressWeight_le_one reply.active.1 m
    have hnonneg : 0 ≤
        (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m) := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg t))
        (by
          unfold vecSq
          exact Finset.sum_nonneg fun j _ => sq_nonneg (d m j))
    exact mul_le_of_le_one_left hnonneg ha
  have hremSum :
      (∑ m, a m * ((9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m))) ≤
        ∑ m, ((9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m)) :=
    Finset.sum_le_sum fun m _ => hremTerm m
  have hscale : 0 ≤ (2 / (N : ℝ)) := by positivity
  have hremScaled := mul_le_mul_of_nonneg_left hremSum hscale
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
  have hremEq :
      (2 / (N : ℝ)) *
          (∑ m, ((9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m))) =
        (9 / 8 : ℝ) * t ^ 2 * blockSq d := by
    rw [blockSq_eq_sum_vecSq, ← Finset.mul_sum]
    simp only [vecSq, WeaklyConvexLowerBound.Foundation.vecSq]
    field_simp [hNreal.ne']
    ring
  rw [hremEq] at hremScaled
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  have hprogress :
      t * ((2 / (N : ℝ)) *
          ∑ m, a m * vecDot (psiGrad (z m)) (d m)) -
          (9 / 8 : ℝ) * t ^ 2 * blockSq d ≤
        branchProgressDifference reply.w y z := by
    unfold branchProgressDifference
    have hsumExpand :
        (∑ m, a m *
          (t * vecDot (psiGrad (z m)) (d m) -
            (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m))) =
          t * (∑ m, a m * vecDot (psiGrad (z m)) (d m)) -
            ∑ m, a m *
              ((9 * (N : ℝ) / 16) * t ^ 2 * vecSq (d m)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro m _
        ring
      · rfl
    rw [hsumExpand] at hscaled
    nlinarith
  have hdot := generalHardFormulaReply_blockDot reply (z + d)
  have hwhole : z + d - z = d := by
    ext m j
    simp
  have hzd (m : Fin M) : (z + d) m - z m = d m := by
    ext j
    simp
  rw [hwhole] at hdot
  simp_rw [hzd] at hdot
  rw [Finset.sum_sub_distrib] at hdot
  have hbranch := activationBranch_sub_eq hA.M_pos reply.w y z
  rw [hfan] at hbranch
  dsimp [a] at hprogress ⊢
  rw [hbranch, hdot]
  nlinarith

theorem exists_hardFormula_line_upper {M N : Nat}
    (hA : Admissible M N) {z d u : BlockVec M N}
    (hR0 : activationNorm z = 0)
    (hu : ∀ m, PhiSubgradient (z m) (u m))
    {t : ℝ} (ht0 : 0 ≤ t)
    (hphi : ∀ m, phi (z m + t • d m) =
      phi (z m) + t * vecDot (u m) (d m))
    (hnegative : ∀ m, sigmaScore z m < 0 →
      sigmaScore (z + t • d) m ≤ 0) :
    ∃ q ∈ hardFormulaSet z,
      hardValue (z + t • d) - hardValue z ≤
        t * blockDot q d + (9 / 8 : ℝ) * t ^ 2 * blockSq d := by
  let y : BlockVec M N := z + t • d
  let w : Fin M → ℝ := canonicalOuterWeight (sigmaScore y)
  have hwactive : ActiveOuterWeight z w := by
    dsimp [w, y]
    exact canonicalOuterWeight_line_active_at_zero hR0 hnegative
  let q : BlockVec M N := hardFormulaParameterMap z (w, u)
  let reply : GeneralHardFormulaReply z q :=
    { w := w
      active := hwactive
      u := u
      u_subgradient := hu
      g_eq := by
        intro m j
        rfl }
  have hq : q ∈ hardFormulaSet z := ⟨reply⟩
  have hupper := reply.activationBranch_line_upper hA ht0 (by
    simpa [reply] using hphi)
  have hcontactY : activationBranch w y = hardValue y := by
    dsimp [w]
    exact activationBranch_canonical_eq_hardValue y
  have hcontactZ : activationBranch w z = hardValue z := by
    unfold activationBranch hardValue
    rw [hwactive.2]
  refine ⟨q, hq, ?_⟩
  dsimp [y] at hcontactY hupper ⊢
  rw [hcontactY, hcontactZ] at hupper
  exact hupper

theorem hardFormulaSet_exists_blockDot_max' {M N : Nat}
    (hN : 0 < N) {z : BlockVec M N} (hR0 : activationNorm z = 0)
    (d : BlockVec M N) :
    ∃ q ∈ hardFormulaSet z,
      ∀ r ∈ hardFormulaSet z, blockDot r d ≤ blockDot q d := by
  have hcontinuous : Continuous (fun q : BlockVec M N => blockDot q d) := by
    unfold blockDot
    fun_prop
  obtain ⟨q, hq, hqmax⟩ :=
    (hardFormulaSet_isCompact hN z).exists_isMaxOn
      (hardFormulaSet_nonempty_of_activationNorm_eq_zero hR0)
      hcontinuous.continuousOn
  exact ⟨q, hq, hqmax⟩

theorem linear_le_of_local_segment_quadratic {A B C ε : ℝ}
    (hε : 0 < ε)
    (h : ∀ t : ℝ, 0 < t → t ≤ ε →
      t * A ≤ t * B + C * t ^ 2) :
    A ≤ B := by
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hδε : δ ≤ ε := min_le_left _ _
  have hscaled : δ * A ≤ δ * B := by
    apply linear_le_of_segment_quadratic (C := C * δ ^ 2)
    intro s hs hs1
    have hδs0 : 0 < δ * s := mul_pos hδ hs
    have hδsε : δ * s ≤ ε := by
      have hs0 : 0 ≤ s := hs.le
      have hmul : δ * s ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left hs1 hδ.le
      nlinarith
    have hmain := h (δ * s) hδs0 hδsε
    nlinarith
  nlinarith

theorem zeroActivationDirectionalDomination_of_fullSubdiff
    {M N : Nat} (hA : Admissible M N) {z g : BlockVec M N}
    (hR0 : activationNorm z = 0)
    (hg : g ∈ fullSubdiff 1 (@hardValue M N) z) :
    ZeroActivationDirectionalDomination z g := by
  intro d
  obtain ⟨u, hu, ε, hε, hlocal⟩ :=
    exists_blockPhiSubgradient_and_score_stability z d
  obtain ⟨q, hq, hqmax⟩ :=
    hardFormulaSet_exists_blockDot_max' hA.N_pos hR0 d
  refine ⟨q, hq, ?_⟩
  rw [mem_fullSubdiff_iff_qSubgradient] at hg
  apply linear_le_of_local_segment_quadratic
    (C := (13 / 8 : ℝ) * blockSq d) hε
  intro t ht htε
  have ht0 : 0 ≤ t := ht.le
  obtain ⟨hphi, hnegative⟩ := hlocal t ht0 htε
  obtain ⟨qt, hqt, hupper⟩ :=
    exists_hardFormula_line_upper hA hR0 hu ht0 hphi hnegative
  have hmax := hqmax qt hqt
  have hqline := hg (z + t • d)
  have hsub : z + t • d - z = t • d := by
    ext m j
    simp
  rw [hsub, blockDot_smul_right_param, blockSq_smul_param] at hqline
  have hupper' :
      hardValue (z + t • d) - hardValue z ≤
        t * blockDot q d + (9 / 8 : ℝ) * t ^ 2 * blockSq d := by
    calc
      _ ≤ t * blockDot qt d + (9 / 8 : ℝ) * t ^ 2 * blockSq d :=
        hupper
      _ ≤ t * blockDot q d + (9 / 8 : ℝ) * t ^ 2 * blockSq d := by
        exact add_le_add (mul_le_mul_of_nonneg_left hmax ht0) le_rfl
  nlinarith

theorem fullSubdiff_subset_hardFormulaSet_of_activation_eq_zero
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (hR0 : activationNorm z = 0) :
    fullSubdiff 1 (@hardValue M N) z ⊆ hardFormulaSet z := by
  intro g hg
  exact mem_hardFormulaSet_of_directional_domination hA.N_pos z g
    (zeroActivationDirectionalDomination_of_fullSubdiff hA hR0 hg)

theorem fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_eq_zero
    {M N : Nat} (hA : Admissible M N) {z : BlockVec M N}
    (hR0 : activationNorm z = 0) :
    fullSubdiff 1 (@hardValue M N) z = convexHull ℝ (hardFormulaSet z) := by
  rw [convexHull_hardFormulaSet_eq]
  exact Set.Subset.antisymm
    (fullSubdiff_subset_hardFormulaSet_of_activation_eq_zero hA hR0)
    (hardFormulaSet_subset_fullSubdiff hA z)

/-- Exact all-point form of Lemma `lem:full-subdiff`, obtained by combining
the positive-activation reconstruction with the zero-activation argument
above. -/
theorem fullSubdiff_eq_convexHull_hardFormulaSet {M N : Nat}
    (hA : Admissible M N) (z : BlockVec M N) :
    fullSubdiff 1 (@hardValue M N) z = convexHull ℝ (hardFormulaSet z) := by
  by_cases hR : 0 < activationNorm z
  · exact fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_pos hA hR
  · have hR0 : activationNorm z = 0 :=
      le_antisymm (le_of_not_gt hR) (activationNorm_nonneg z)
    exact fullSubdiff_eq_convexHull_hardFormulaSet_of_activation_eq_zero
      hA hR0

end

end WeaklyConvexLowerBound

