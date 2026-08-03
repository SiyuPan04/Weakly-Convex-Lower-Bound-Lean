import WeaklyConvexLowerBound.HardInstance
import WeaklyConvexLowerBound.BarrierAlgebra
import WeaklyConvexLowerBound.Progress

/-!
# Explicit formula replies at positive activation

When `activationNorm z > 0`, the positive activation vector has one canonical
normalization.  This file inserts that normalization and the paper's
blockwise formula into `BarrierAlgebraData`, thereby proving the algebraic
stationarity barrier for every explicit formula reply.

No claim identifying these formula replies with a standard limiting or
Clarke subdifferential is made here.  That semantic identification is exposed
at the end as an explicit bridge proposition for a later analytic layer.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The unique normalized positive-activation weight at block `m`. -/
def activeWeight {M N : Nat} (z : BlockVec M N) (m : Fin M) : ℝ :=
  max (sigmaScore z m) 0 / activationNorm z

/-- The next normalized weight, with the manuscript's terminal convention
`w_{M+1}=0`. -/
def nextActiveWeight {M N : Nat} (z : BlockVec M N) (m : Fin M) : ℝ :=
  if hm : m.1 + 1 < M then activeWeight z ⟨m.1 + 1, hm⟩ else 0

/-- The net progress coefficient `a_m = 1 - w_{m+1}`. -/
def netCoefficient {M N : Nat} (z : BlockVec M N) (m : Fin M) : ℝ :=
  1 - nextActiveWeight z m

theorem activeWeight_nonneg {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M) :
    0 ≤ activeWeight z m := by
  unfold activeWeight
  exact div_nonneg (le_max_right _ _) hR.le

/-- The normalized positive part lies on the Euclidean unit sphere. -/
theorem activeWeight_sq_sum {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) :
    (∑ m, (activeWeight z m) ^ 2) = 1 := by
  have hsum0 : 0 ≤ ∑ m : Fin M, (max (sigmaScore z m) 0) ^ 2 :=
    Finset.sum_nonneg fun m _ ↦ sq_nonneg (max (sigmaScore z m) 0)
  have hR2 : activationNorm z ^ 2 =
      ∑ m : Fin M, (max (sigmaScore z m) 0) ^ 2 := by
    unfold activationNorm
    exact Real.sq_sqrt hsum0
  simp only [activeWeight, div_pow]
  rw [← Finset.sum_div, ← hR2,
    div_self (pow_ne_zero 2 hR.ne')]

theorem activeWeight_le_one {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M) :
    activeWeight z m ≤ 1 := by
  have hsingle : (activeWeight z m) ^ 2 ≤
      ∑ i : Fin M, (activeWeight z i) ^ 2 :=
    Finset.single_le_sum
      (fun i _ ↦ sq_nonneg (activeWeight z i)) (Finset.mem_univ m)
  rw [activeWeight_sq_sum hR] at hsingle
  have hnonneg := activeWeight_nonneg hR m
  nlinarith

theorem nextActiveWeight_nonneg {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M) :
    0 ≤ nextActiveWeight z m := by
  unfold nextActiveWeight
  split
  · exact activeWeight_nonneg hR _
  · norm_num

theorem nextActiveWeight_le_one {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M) :
    nextActiveWeight z m ≤ 1 := by
  unfold nextActiveWeight
  split
  · exact activeWeight_le_one hR _
  · norm_num

theorem netCoefficient_nonneg {M N : Nat} {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M) :
    0 ≤ netCoefficient z m := by
  unfold netCoefficient
  linarith [nextActiveWeight_le_one hR m]

theorem previousProgress_le_one {M N : Nat} (hN : 0 < N)
    (z : BlockVec M N) (m : Fin M) : previousProgress z m ≤ 1 := by
  unfold previousProgress
  split
  · norm_num
  · exact psi_le_one hN _

/-- A nonzero normalized activation weight forces `sigma_m > 0`, hence
`phi(z^m) > 0`; the constant zero facet is therefore inactive. -/
theorem zeroFacet_inactive_of_activeWeight_ne_zero {M N : Nat}
    (hN : 0 < N) {z : BlockVec M N}
    (hR : 0 < activationNorm z) (m : Fin M)
    (hw : activeWeight z m ≠ 0) :
    ¬ActiveFacet (z m) (none : FacetIndex N) := by
  have hw0 := activeWeight_nonneg hR m
  have hwpos : 0 < activeWeight z m :=
    lt_of_le_of_ne hw0 (Ne.symm hw)
  have hcancel : activeWeight z m * activationNorm z =
      max (sigmaScore z m) 0 := by
    unfold activeWeight
    field_simp [hR.ne']
  have hmax : 0 < max (sigmaScore z m) 0 := by
    rw [← hcancel]
    exact mul_pos hwpos hR
  have hsigma : 0 < sigmaScore z m := by
    by_contra hs
    have hsle : sigmaScore z m ≤ 0 := le_of_not_gt hs
    rw [max_eq_right hsle] at hmax
    exact (lt_irrefl 0) hmax
  have hprev := previousProgress_le_one hN z m
  have hphi : 0 < phi (z m) := by
    unfold sigmaScore at hsigma
    linarith
  exact none_not_active_of_phi_pos hphi

/-- A formula reply carries one tilted-block subgradient per block and the
literal block formula from TeX equation `eq:block-subgradient`. -/
structure HardFormulaReply {M N : Nat} (z g : BlockVec M N) where
  u : BlockVec M N
  u_subgradient : ∀ m, PhiSubgradient (z m) (u m)
  g_eq : ∀ m j, g m j =
    (2 / (N : ℝ)) *
      (activeWeight z m * u m j - netCoefficient z m * psiGrad (z m) j)

/-- Every positive-activation formula reply supplies all fields required by
the already-verified finite-sum barrier. -/
def HardFormulaReply.toBarrierAlgebraData {M N : Nat}
    {z g : BlockVec M N} (hN : 0 < N) (hR : 0 < activationNorm z)
    (reply : HardFormulaReply z g) : BarrierAlgebraData M N where
  point := z
  u := reply.u
  weights := activeWeight z
  a := netCoefficient z
  progressGrad := fun m ↦ psiGrad (z m)
  g := g
  u_subgradient := reply.u_subgradient
  zero_inactive := fun m hw ↦
    zeroFacet_inactive_of_activeWeight_ne_zero hN hR m hw
  weights_nonneg := activeWeight_nonneg hR
  weights_sq_sum := activeWeight_sq_sum hR
  a_nonneg := netCoefficient_nonneg hR
  progressGrad_nonneg := fun m j ↦ psiGrad_nonneg (z m) j
  g_eq := reply.g_eq

/-- Algebraic stationarity barrier for the explicit formula reply. -/
theorem hardFormulaReply_barrier {M N : Nat} {z g : BlockVec M N}
    (hN : 0 < N) (hR : 0 < activationNorm z)
    (reply : HardFormulaReply z g) :
    1 ≤ 16 * (N : ℝ) * blockSq g := by
  exact barrier_algebra hN (reply.toBarrierAlgebraData hN hR)

/-! ## Explicit external bridge obligation -/

/-- A semantic subdifferential set agrees with the formula model at `z`.

This is a *proposition to be supplied* by a future limiting/Clarke
subdifferential development.  This file neither assumes nor proves it. -/
def FormulaReplyBridge {M N : Nat} (z : BlockVec M N)
    (standardSubdiff : Set (BlockVec M N)) : Prop :=
  ∀ g, g ∈ standardSubdiff ↔ Nonempty (HardFormulaReply z g)

/-- Conditional transfer showing exactly how the external semantic bridge
would turn the formula barrier into a full-subdifferential barrier. -/
theorem standardSubdiff_barrier_of_bridge {M N : Nat}
    {z g : BlockVec M N} {standardSubdiff : Set (BlockVec M N)}
    (hN : 0 < N) (hR : 0 < activationNorm z)
    (hbridge : FormulaReplyBridge z standardSubdiff)
    (hg : g ∈ standardSubdiff) :
    1 ≤ 16 * (N : ℝ) * blockSq g := by
  obtain ⟨reply⟩ := (hbridge g).1 hg
  exact hardFormulaReply_barrier hN hR reply

end

end WeaklyConvexLowerBound

