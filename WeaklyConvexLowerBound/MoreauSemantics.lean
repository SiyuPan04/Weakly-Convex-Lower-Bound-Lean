import WeaklyConvexLowerBound.TerminalFiltration
import WeaklyConvexLowerBound.Regularity
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Genuine semantics of the half Moreau envelope

The proximal residual used in the terminal argument is connected here to the
actual infimal-convolution envelope.  The domain is the finite block space and
all quadratic estimates use `blockSq`, rather than the ambient product sup
norm.  The latter is used only at the final Fréchet-topology bridge.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Asymptotics
open scoped BigOperators

/-! ## The infimum and existence of its minimizer -/

/-- Objective defining the Moreau envelope with parameter `1 / 2`. -/
def halfProxObjective {M N : Nat} (f : BlockVec M N → ℝ)
    (y z : BlockVec M N) : ℝ :=
  f z + blockSq (z - y)

@[simp] theorem isHalfProxPoint_iff {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N} :
    IsHalfProxPoint f y z ↔
      ∀ x, halfProxObjective f y z ≤ halfProxObjective f y x := by
  rfl

/-- The genuine half Moreau envelope, defined as an infimum over all points. -/
def halfMoreauEnvelope {M N : Nat} (f : BlockVec M N → ℝ)
    (y : BlockVec M N) : ℝ :=
  sInf (Set.range (halfProxObjective f y))

/-- Existence of an attained half-proximal point at every anchor. -/
def HasHalfProxEverywhere {M N : Nat} (f : BlockVec M N → ℝ) : Prop :=
  ∀ y, ∃ z, IsHalfProxPoint f y z

/-- A selected proximal map.  Weak convexity below proves that the selection
is independent of classical choice. -/
def halfProxMap {M N : Nat} {f : BlockVec M N → ℝ}
    (hexists : HasHalfProxEverywhere f) (y : BlockVec M N) : BlockVec M N :=
  Classical.choose (hexists y)

theorem halfProxMap_spec {M N : Nat} {f : BlockVec M N → ℝ}
    (hexists : HasHalfProxEverywhere f) (y : BlockVec M N) :
    IsHalfProxPoint f y (halfProxMap hexists y) :=
  Classical.choose_spec (hexists y)

/-- A coordinate square is bounded by the full block sum of squares. -/
theorem coordinate_sq_le_blockSq {M N : Nat} (x : BlockVec M N)
    (m : Fin M) (j : Fin N) :
    x m j ^ 2 ≤ blockSq x := by
  unfold blockSq
  calc
    x m j ^ 2 ≤ ∑ k : Fin N, x m k ^ 2 :=
      Finset.single_le_sum (fun k _ ↦ sq_nonneg (x m k))
        (Finset.mem_univ j)
    _ ≤ ∑ i : Fin M, ∑ k : Fin N, x i k ^ 2 :=
      Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg (x i k))
        (Finset.mem_univ m)

/-- The product sup norm is no larger than the explicit Euclidean norm. -/
theorem norm_le_sqrt_blockSq {M N : Nat} (x : BlockVec M N) :
    ‖x‖ ≤ Real.sqrt (blockSq x) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro m
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro j
  have hc := coordinate_sq_le_blockSq x m j
  have hs0 := Real.sqrt_nonneg (blockSq x)
  have hs2 := Real.sq_sqrt (blockSq_nonneg x)
  have habs : |x m j| ≤ Real.sqrt (blockSq x) := by
    nlinarith [sq_abs (x m j), abs_nonneg (x m j)]
  simpa only [Real.norm_eq_abs] using habs

/-- Conversely, the finite coordinate sum is controlled by the product sup
norm.  This is the quantitative bridge used in the Fréchet proof. -/
theorem blockSq_le_card_mul_norm_sq {M N : Nat} (x : BlockVec M N) :
    blockSq x ≤ ((M * N : Nat) : ℝ) * ‖x‖ ^ 2 := by
  unfold blockSq
  calc
    (∑ m : Fin M, ∑ j : Fin N, x m j ^ 2) ≤
        ∑ _m : Fin M, ∑ _j : Fin N, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro j _
      have hjm : ‖x m j‖ ≤ ‖x m‖ := norm_le_pi_norm (x m) j
      have hm : ‖x m‖ ≤ ‖x‖ := norm_le_pi_norm x m
      have hj : |x m j| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using hjm.trans hm
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (x m j)) (norm_nonneg x)).2 hj
    _ = ((M * N : Nat) : ℝ) * ‖x‖ ^ 2 := by
      simp
      ring

/-- Euclidean Lipschitz continuity from `Framework` implies ordinary
topological continuity on the finite product. -/
theorem EuclideanLipschitz.continuous {M N : Nat} {C : ℝ}
    {f : BlockVec M N → ℝ} (hC : 0 ≤ C)
    (hf : EuclideanLipschitz C f) : Continuous f := by
  let K : ℝ := ((M * N : Nat) : ℝ)
  let L : ℝ := C * Real.sqrt K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := mul_nonneg hC (Real.sqrt_nonneg K)
  have hLip : LipschitzWith (Real.toNNReal L) f := by
    intro x y
    have hv := hf x y
    have hs := blockSq_le_card_mul_norm_sq (x - y)
    have hprod :
        C ^ 2 * blockSq (x - y) ≤
          C ^ 2 * (K * ‖x - y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg C)
    have hbound :
        (f x - f y) ^ 2 ≤ (L * ‖x - y‖) ^ 2 := by
      have hsqrt := Real.sq_sqrt hK
      dsimp [L]
      calc
        (f x - f y) ^ 2 ≤ C ^ 2 * blockSq (x - y) := hv
        _ ≤ C ^ 2 * (K * ‖x - y‖ ^ 2) := hprod
        _ = (C * Real.sqrt K * ‖x - y‖) ^ 2 := by
          rw [mul_pow, mul_pow, hsqrt]
          ring
    have hright : 0 ≤ L * ‖x - y‖ := mul_nonneg hL (norm_nonneg _)
    have habs : |f x - f y| ≤ L * ‖x - y‖ := by
      apply (sq_le_sq₀ (abs_nonneg (f x - f y)) hright).mp
      simpa [sq_abs] using hbound
    rw [edist_dist, edist_dist, ENNReal.ofNNReal_toNNReal,
      ← ENNReal.ofReal_mul hL]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [Real.dist_eq, dist_eq_norm] using habs)
  exact hLip.continuous

theorem continuous_blockSq {M N : Nat} :
    Continuous (@blockSq M N) := by
  unfold blockSq
  fun_prop

theorem continuous_halfProxObjective {M N : Nat}
    {f : BlockVec M N → ℝ} (hf : Continuous f) (y : BlockVec M N) :
    Continuous (halfProxObjective f y) := by
  unfold halfProxObjective
  exact hf.add (continuous_blockSq.comp (continuous_id.sub continuous_const))

/-- A continuous globally lower-bounded finite-dimensional function attains
every half-proximal objective.  The proof minimizes first on a sufficiently
large compact ball and shows that points outside it have larger objective. -/
theorem exists_halfProxPoint_of_continuous_bddBelow {M N : Nat}
    {f : BlockVec M N → ℝ} {lower : ℝ}
    (hf : Continuous f) (hlower : ∀ x, lower ≤ f x)
    (y : BlockVec M N) :
    ∃ z, IsHalfProxPoint f y z := by
  let x0 : BlockVec M N := 0
  let R2 : ℝ := blockSq (x0 - y) + (f x0 - lower + 1)
  have hgap0 : 0 ≤ f x0 - lower := sub_nonneg.mpr (hlower x0)
  have hR2 : 0 ≤ R2 := by
    dsimp [R2]
    exact add_nonneg (blockSq_nonneg _) (by linarith)
  let K : Set (BlockVec M N) := Metric.closedBall y (Real.sqrt R2)
  have hKcompact : IsCompact K := isCompact_closedBall y (Real.sqrt R2)
  have hx0ball : x0 ∈ K := by
    dsimp [K]
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsq : blockSq (x0 - y) ≤ R2 := by
      dsimp [R2]
      linarith
    exact (norm_le_sqrt_blockSq (x0 - y)).trans (Real.sqrt_le_sqrt hsq)
  have hKne : K.Nonempty := ⟨x0, hx0ball⟩
  obtain ⟨z, hzK, hminK⟩ := hKcompact.exists_isMinOn hKne
    (continuous_halfProxObjective hf y).continuousOn
  refine ⟨z, ?_⟩
  intro v
  by_cases hvball : v ∈ K
  · exact hminK hvball
  · have hdist : Real.sqrt R2 < dist v y := by
      simpa [K, Metric.mem_closedBall] using hvball
    have hnorm : ‖v - y‖ ≤ Real.sqrt (blockSq (v - y)) :=
      norm_le_sqrt_blockSq (v - y)
    have hsqrtlt : Real.sqrt R2 < Real.sqrt (blockSq (v - y)) := by
      rw [dist_eq_norm] at hdist
      exact hdist.trans_le hnorm
    have hvsq : R2 < blockSq (v - y) := by
      have hsR := Real.sq_sqrt hR2
      have hsv := Real.sq_sqrt (blockSq_nonneg (v - y))
      nlinarith [Real.sqrt_nonneg R2,
        Real.sqrt_nonneg (blockSq (v - y))]
    have hx0min : halfProxObjective f y z ≤ halfProxObjective f y x0 :=
      hminK hx0ball
    have hvlarge : halfProxObjective f y x0 < halfProxObjective f y v := by
      have hvlow := hlower v
      unfold halfProxObjective
      dsimp [R2] at hvsq
      nlinarith
    exact hx0min.trans hvlarge.le

theorem hasHalfProxEverywhere_of_continuous_bddBelow {M N : Nat}
    {f : BlockVec M N → ℝ} {lower : ℝ}
    (hf : Continuous f) (hlower : ∀ x, lower ≤ f x) :
    HasHalfProxEverywhere f := by
  intro y
  exact exists_halfProxPoint_of_continuous_bddBelow hf hlower y

theorem hasHalfProxEverywhere_of_continuous_range_bddBelow {M N : Nat}
    {f : BlockVec M N → ℝ} (hf : Continuous f)
    (hlower : BddBelow (Set.range f)) :
    HasHalfProxEverywhere f := by
  rcases hlower with ⟨lower, hlower⟩
  exact hasHalfProxEverywhere_of_continuous_bddBelow hf
    (fun x ↦ hlower (Set.mem_range_self x))

/-- An attained proximal value really is the infimum in the definition. -/
theorem halfMoreauEnvelope_eq_at_prox {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) :
    halfMoreauEnvelope f y = halfProxObjective f y z := by
  unfold halfMoreauEnvelope
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨z, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact hz x

theorem halfMoreauEnvelope_eq_selected {M N : Nat}
    {f : BlockVec M N → ℝ} (hexists : HasHalfProxEverywhere f)
    (y : BlockVec M N) :
    halfMoreauEnvelope f y =
      halfProxObjective f y (halfProxMap hexists y) :=
  halfMoreauEnvelope_eq_at_prox (halfProxMap_spec hexists y)

/-! ## Strong proximal minimality and uniqueness -/

private theorem halfProxResidual_dot_displacement {M N : Nat}
    (x y z : BlockVec M N) :
    blockDot (halfProxResidual y z) (x - z) =
      -2 * blockDot (x - z) (z - y) := by
  unfold halfProxResidual
  rw [blockDot_smul_left, blockDot_comm (y - z) (x - z)]
  have hneg : y - z = -(z - y) := by
    ext m j
    simp
  rw [hneg]
  unfold blockDot
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

/-- For a `1`-weakly convex function, half-proximal minimality has a genuine
quadratic growth gap of coefficient `1/2`. -/
theorem IsHalfProxPoint.strong_minimizer_of_weaklyConvex {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) (hweak : WeaklyConvex 1 f)
    (x : BlockVec M N) :
    halfProxObjective f y z + (1 / 2 : ℝ) * blockSq (x - z) ≤
      halfProxObjective f y x := by
  have hsupp := hz.residual_qSubgradient_half_of_weaklyConvex hweak x
  have hthree := blockSq_three_point x y z
  have hdot := halfProxResidual_dot_displacement x y z
  unfold halfProxObjective
  nlinarith

/-- Vanishing explicit Euclidean square is equivalent to vanishing vector. -/
theorem blockSq_eq_zero_iff {M N : Nat} {x : BlockVec M N} :
    blockSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext m j
    have hc := coordinate_sq_le_blockSq x m j
    have : x m j = 0 := by nlinarith [sq_nonneg (x m j)]
    simpa using this
  · rintro rfl
    simp [blockSq]

/-- The half-proximal point is unique under `1`-weak convexity. -/
theorem halfProxPoint_unique_of_weaklyConvex {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    {y z w : BlockVec M N}
    (hz : IsHalfProxPoint f y z) (hw : IsHalfProxPoint f y w) :
    z = w := by
  have hstrong := hz.strong_minimizer_of_weaklyConvex hweak w
  have hmin := hw z
  unfold halfProxObjective at hstrong
  have hsq0 : blockSq (w - z) = 0 := by
    have hs := blockSq_nonneg (w - z)
    nlinarith
  have hzero : w - z = 0 := blockSq_eq_zero_iff.mp hsq0
  exact (sub_eq_zero.mp hzero).symm

theorem halfProxMap_unique {M N : Nat} {f : BlockVec M N → ℝ}
    (hweak : WeaklyConvex 1 f) (hexists : HasHalfProxEverywhere f)
    {y z : BlockVec M N} (hz : IsHalfProxPoint f y z) :
    halfProxMap hexists y = z :=
  halfProxPoint_unique_of_weaklyConvex hweak
    (halfProxMap_spec hexists y) hz

/-- Under the explicit analytic hypotheses used for existence, the proximal
minimizer exists and is unique. -/
theorem existsUnique_halfProxPoint_of_continuous_bddBelow_weaklyConvex
    {M N : Nat} {f : BlockVec M N → ℝ} {lower : ℝ}
    (hf : Continuous f) (hlower : ∀ x, lower ≤ f x)
    (hweak : WeaklyConvex 1 f) (y : BlockVec M N) :
    ∃! z, IsHalfProxPoint f y z := by
  obtain ⟨z, hz⟩ := exists_halfProxPoint_of_continuous_bddBelow
    hf hlower y
  refine ⟨z, hz, ?_⟩
  intro w hw
  exact halfProxPoint_unique_of_weaklyConvex hweak hw hz

/-! ## Proximal displacement and residual regularity -/

theorem blockDot_sub_left {M N : Nat} (x y h : BlockVec M N) :
    blockDot (x - y) h = blockDot x h - blockDot y h := by
  unfold blockDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

theorem blockSq_sub_expand {M N : Nat} (x y : BlockVec M N) :
    blockSq (x - y) =
      blockSq x - 2 * blockDot x y + blockSq y := by
  unfold blockSq blockDot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

theorem blockSq_sub_comm' {M N : Nat} (x y : BlockVec M N) :
    blockSq (x - y) = blockSq (y - x) := by
  unfold blockSq
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

theorem blockSq_four_point {M N : Nat}
    (u v y w : BlockVec M N) :
    blockSq (v - y) + blockSq (u - w) -
        blockSq (u - y) - blockSq (v - w) =
      2 * blockDot (y - w) (u - v) := by
  unfold blockSq blockDot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

/-- Weak monotonicity of two proximal points. -/
theorem halfProx_displacement_inequality {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y w : BlockVec M N) :
    blockSq (halfProxMap hexists y - halfProxMap hexists w) ≤
      2 * blockDot (y - w)
        (halfProxMap hexists y - halfProxMap hexists w) := by
  let u := halfProxMap hexists y
  let v := halfProxMap hexists w
  have hu := halfProxMap_spec hexists y
  have hv := halfProxMap_spec hexists w
  have hy := hu.strong_minimizer_of_weaklyConvex hweak v
  have hw := hv.strong_minimizer_of_weaklyConvex hweak u
  have hfour := blockSq_four_point u v y w
  dsimp [u, v] at hy hw hfour ⊢
  rw [blockSq_sub_comm' (halfProxMap hexists w)
    (halfProxMap hexists y)] at hy
  unfold halfProxObjective at hy hw
  nlinarith

/-- The displacement residual `y - prox y` is nonexpansive in explicit
Euclidean squared norm. -/
theorem halfProxResidual_nonexpansive {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y w : BlockVec M N) :
    blockSq ((y - halfProxMap hexists y) -
        (w - halfProxMap hexists w)) ≤ blockSq (y - w) := by
  have hmono := halfProx_displacement_inequality hweak hexists y w
  have hid :
      (y - halfProxMap hexists y) - (w - halfProxMap hexists w) =
        (y - w) -
          (halfProxMap hexists y - halfProxMap hexists w) := by
    abel
  rw [hid, blockSq_sub_expand]
  linarith [blockSq_nonneg
    (halfProxMap hexists y - halfProxMap hexists w)]

private theorem blockSq_sub_le_two {M N : Nat}
    (a b : BlockVec M N) :
    blockSq (a - b) ≤ 2 * blockSq a + 2 * blockSq b := by
  unfold blockSq
  calc
    (∑ m : Fin M, ∑ j : Fin N, (a - b) m j ^ 2) ≤
        ∑ m : Fin M, ∑ j : Fin N,
          (2 * (a m j) ^ 2 + 2 * (b m j) ^ 2) := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro j _
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (a m j + b m j)]
    _ = 2 * (∑ m : Fin M, ∑ j : Fin N, a m j ^ 2) +
        2 * (∑ m : Fin M, ∑ j : Fin N, b m j ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The selected proximal map is `2`-Lipschitz in squared Euclidean form. -/
theorem halfProxMap_lipschitz_sq {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y w : BlockVec M N) :
    blockSq (halfProxMap hexists y - halfProxMap hexists w) ≤
      4 * blockSq (y - w) := by
  let r := (y - halfProxMap hexists y) -
    (w - halfProxMap hexists w)
  have hr := halfProxResidual_nonexpansive hweak hexists y w
  have hid :
      halfProxMap hexists y - halfProxMap hexists w = (y - w) - r := by
    dsimp [r]
    abel
  rw [hid]
  have htwo := blockSq_sub_le_two (y - w) r
  change blockSq r ≤ blockSq (y - w) at hr
  linarith

/-! ## The actual envelope derivative -/

/-- The Euclidean vector represented by the derivative of the envelope. -/
def halfMoreauGradient {M N : Nat} {f : BlockVec M N → ℝ}
    (hexists : HasHalfProxEverywhere f) (y : BlockVec M N) :
    BlockVec M N :=
  halfProxResidual y (halfProxMap hexists y)

theorem halfMoreauGradient_eq_residual_of_prox {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) :
    halfMoreauGradient hexists y = halfProxResidual y z := by
  unfold halfMoreauGradient
  rw [halfProxMap_unique hweak hexists hz]

/-- Continuous linear functional represented by `blockDot g`. -/
def blockGradientCLM {M N : Nat} (g : BlockVec M N) :
    BlockVec M N →L[ℝ] ℝ := by
  letI : AddCommGroup (BlockVec M N) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (BlockVec M N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (BlockVec M N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h : BlockVec M N ↦ blockDot g h
       map_add' := by
         intro x y
         unfold blockDot
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro m _
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro j _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c x
         unfold blockDot
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro m _
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro j _
         ring } : BlockVec M N →ₗ[ℝ] ℝ)

@[simp] theorem blockGradientCLM_apply {M N : Nat}
    (g h : BlockVec M N) :
    blockGradientCLM g h = blockDot g h := rfl

theorem blockSq_anchor_add {M N : Nat}
    (u y h : BlockVec M N) :
    blockSq (u - (y + h)) =
      blockSq (u - y) - 2 * blockDot (u - y) h + blockSq h := by
  unfold blockSq blockDot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

private theorem blockSq_smul_moreau {M N : Nat}
    (c : ℝ) (x : BlockVec M N) :
    blockSq (c • x) = c ^ 2 * blockSq x := by
  unfold blockSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Direct two-sided-minimality estimate for the actual infimum envelope. -/
theorem halfMoreauEnvelope_remainder_abs_le {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y h : BlockVec M N) :
    |halfMoreauEnvelope f (y + h) - halfMoreauEnvelope f y -
        blockGradientCLM (halfMoreauGradient hexists y) h| ≤
      blockSq h := by
  let u := halfProxMap hexists y
  let v := halfProxMap hexists (y + h)
  have hu := halfProxMap_spec hexists y
  have hv := halfProxMap_spec hexists (y + h)
  have hupper := hv u
  have hlower := hu.strong_minimizer_of_weaklyConvex hweak v
  have hanchorU := blockSq_anchor_add u y h
  have hanchorV := blockSq_anchor_add v y h
  have hsquare := blockSq_nonneg ((v - u) - (2 : ℝ) • h)
  have hsquareId :
      blockSq ((v - u) - (2 : ℝ) • h) =
        blockSq (v - u) - 4 * blockDot (v - u) h +
          4 * blockSq h := by
    unfold blockSq blockDot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsquareId] at hsquare
  rw [halfMoreauEnvelope_eq_selected hexists (y + h),
    halfMoreauEnvelope_eq_selected hexists y]
  rw [blockGradientCLM_apply]
  unfold halfMoreauGradient halfProxResidual
  have hdot :
      blockDot ((2 : ℝ) • (y - u)) h =
        2 * blockDot (y - u) h := by
    rw [blockDot_smul_left]
  have hsign : blockDot (y - u) h = -blockDot (u - y) h := by
    rw [blockDot_sub_left, blockDot_sub_left]
    ring
  have hdiff : blockDot (v - u) h =
      blockDot (v - y) h - blockDot (u - y) h := by
    rw [blockDot_sub_left, blockDot_sub_left, blockDot_sub_left]
    ring
  dsimp [u, v] at hanchorU hanchorV hupper hlower hsquare hsign hdiff ⊢
  simp only [halfProxObjective] at hlower ⊢
  rw [hanchorU] at hupper
  rw [hdot]
  rw [abs_le]
  constructor <;>
    nlinarith [hanchorV, hsign, hdiff, blockSq_nonneg h]

/-- The envelope has the genuine Fréchet derivative represented by the
proximal residual.  The proof passes from the explicit Euclidean quadratic
remainder to the finite-product norm using
`blockSq_le_card_mul_norm_sq`. -/
theorem hasFDerivAt_halfMoreauEnvelope {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y : BlockVec M N) :
    HasFDerivAt (halfMoreauEnvelope f)
      (blockGradientCLM (halfMoreauGradient hexists y)) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbigO :
      (fun h : BlockVec M N ↦
        halfMoreauEnvelope f (y + h) - halfMoreauEnvelope f y -
          blockGradientCLM (halfMoreauGradient hexists y) h) =O[nhds 0]
        (fun h : BlockVec M N ↦ ‖h‖ ^ 2) := by
    rw [isBigO_iff]
    refine ⟨((M * N : Nat) : ℝ), ?_⟩
    filter_upwards [] with h
    have hrem := halfMoreauEnvelope_remainder_abs_le
      hweak hexists y h
    have hsq := blockSq_le_card_mul_norm_sq h
    rw [Real.norm_eq_abs]
    calc
      |halfMoreauEnvelope f (y + h) - halfMoreauEnvelope f y -
          blockGradientCLM (halfMoreauGradient hexists y) h| ≤
          blockSq h := hrem
      _ ≤ ((M * N : Nat) : ℝ) * ‖h‖ ^ 2 := hsq
      _ = ((M * N : Nat) : ℝ) * |‖h‖ ^ 2| := by
        rw [abs_of_nonneg (sq_nonneg ‖h‖)]
  exact hbigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

theorem fderiv_halfMoreauEnvelope_eq {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y : BlockVec M N) :
    fderiv ℝ (halfMoreauEnvelope f) y =
      blockGradientCLM (halfMoreauGradient hexists y) :=
  (hasFDerivAt_halfMoreauEnvelope hweak hexists y).fderiv

theorem differentiable_halfMoreauEnvelope {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) :
    Differentiable ℝ (halfMoreauEnvelope f) := by
  intro y
  exact (hasFDerivAt_halfMoreauEnvelope hweak hexists y).differentiableAt

/-- Squared Euclidean Lipschitz estimate for the actual envelope-gradient
field (`2` is the norm Lipschitz constant). -/
theorem halfMoreauGradient_lipschitz_sq {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) (y w : BlockVec M N) :
    blockSq (halfMoreauGradient hexists y -
        halfMoreauGradient hexists w) ≤
      4 * blockSq (y - w) := by
  have hr := halfProxResidual_nonexpansive hweak hexists y w
  have heq :
      halfMoreauGradient hexists y - halfMoreauGradient hexists w =
        (2 : ℝ) • ((y - halfProxMap hexists y) -
          (w - halfProxMap hexists w)) := by
    unfold halfMoreauGradient halfProxResidual
    ext m j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, blockSq_smul_moreau]
  nlinarith

/-- The hypotheses used by the existence theorem can be discharged before
invoking the Fréchet derivative theorem; no proximal-existence assumption is
left unproved. -/
theorem exists_global_halfProx_semantics {M N : Nat}
    {f : BlockVec M N → ℝ} {lower : ℝ}
    (hf : Continuous f) (hlower : ∀ x, lower ≤ f x)
    (hweak : WeaklyConvex 1 f) :
    ∃ hexists : HasHalfProxEverywhere f,
      ∀ y, HasFDerivAt (halfMoreauEnvelope f)
        (blockGradientCLM (halfMoreauGradient hexists y)) y := by
  let hexists : HasHalfProxEverywhere f :=
    hasHalfProxEverywhere_of_continuous_bddBelow hf hlower
  refine ⟨hexists, ?_⟩
  intro y
  exact hasFDerivAt_halfMoreauEnvelope hweak hexists y

/-! ## Euclidean norm of the derivative vector -/

/-- The explicit Euclidean norm belonging to `blockSq`. -/
def blockEuclideanNorm {M N : Nat} (x : BlockVec M N) : ℝ :=
  Real.sqrt (blockSq x)

theorem blockEuclideanNorm_sq {M N : Nat} (x : BlockVec M N) :
    blockEuclideanNorm x ^ 2 = blockSq x := by
  exact Real.sq_sqrt (blockSq_nonneg x)

/-- The squared Euclidean norm of the actual envelope-gradient vector is
literally the squared proximal residual used in the terminal theorem. -/
theorem halfMoreauGradient_euclidean_norm_sq {M N : Nat}
    {f : BlockVec M N → ℝ} (hexists : HasHalfProxEverywhere f)
    (y : BlockVec M N) :
    blockEuclideanNorm (halfMoreauGradient hexists y) ^ 2 =
      blockSq (halfProxResidual y (halfProxMap hexists y)) := by
  rw [blockEuclideanNorm_sq]
  rfl

/-- Selection-free form: for any proximal minimizer, its residual is the
unique derivative vector and its `blockSq` is the squared Euclidean norm of
the Moreau gradient. -/
theorem halfMoreauGradient_euclidean_norm_sq_of_prox {M N : Nat}
    {f : BlockVec M N → ℝ} (hweak : WeaklyConvex 1 f)
    (hexists : HasHalfProxEverywhere f) {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) :
    blockEuclideanNorm (halfMoreauGradient hexists y) ^ 2 =
      blockSq (halfProxResidual y z) := by
  rw [blockEuclideanNorm_sq,
    halfMoreauGradient_eq_residual_of_prox hweak hexists hz]

/-! ## Concrete instantiation for the manuscript's hard value -/

/-- The C1 regularity theorems discharge the analytic existence assumptions
for the literal normalized hard instance. -/
theorem hardValueHalfProxExistence {M N : Nat} (hA : Admissible M N) :
    HasHalfProxEverywhere (@hardValue M N) :=
  hasHalfProxEverywhere_of_continuous_range_bddBelow
    ((hardValue_euclideanLipschitz hA).continuous (by norm_num))
    (hardValue_range_bddBelow hA.N_pos)

theorem hardValue_halfProxMap_spec {M N : Nat} (hA : Admissible M N)
    (y : BlockVec M N) :
    IsHalfProxPoint hardValue y
      (halfProxMap (hardValueHalfProxExistence hA) y) :=
  halfProxMap_spec (hardValueHalfProxExistence hA) y

/-- The concrete hard function's genuine half-Moreau envelope is Fréchet
differentiable, with derivative represented by its selected residual. -/
theorem hasFDerivAt_hardValue_halfMoreauEnvelope {M N : Nat}
    (hA : Admissible M N) (y : BlockVec M N) :
    HasFDerivAt (halfMoreauEnvelope (@hardValue M N))
      (blockGradientCLM
        (halfMoreauGradient (hardValueHalfProxExistence hA) y)) y :=
  hasFDerivAt_halfMoreauEnvelope (hardValue_one_weaklyConvex hA)
    (hardValueHalfProxExistence hA) y

theorem hardValue_halfMoreauGradient_euclidean_norm_sq {M N : Nat}
    (hA : Admissible M N) (y : BlockVec M N) :
    blockEuclideanNorm
        (halfMoreauGradient (hardValueHalfProxExistence hA) y) ^ 2 =
      blockSq (halfProxResidual y
        (halfProxMap (hardValueHalfProxExistence hA) y)) :=
  halfMoreauGradient_euclidean_norm_sq
    (hardValueHalfProxExistence hA) y

end

end WeaklyConvexLowerBound

