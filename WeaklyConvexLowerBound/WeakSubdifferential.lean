import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.QuadraticSubgradient
import WeaklyConvexLowerBound.CoreFunctions
import WeaklyConvexLowerBound.Progress
import WeaklyConvexLowerBound.Variational
import WeaklyConvexLowerBound.FormulaLocality

/-!
# The full subdifferential of a weakly convex function

For a `ρ`-weakly convex finite-valued function `f`, its convexification

`x ↦ f x + (ρ / 2) * ‖x‖²`

is convex.  The standard limiting, proximal, and Clarke subdifferentials
then agree and can be represented without importing an unavailable
nonsmooth-analysis API: take the ordinary convex support subgradient of the
convexification and translate it by the gradient `ρ z` of the quadratic.

The main result of the first section is not a definition-by-fiat bridge:
`mem_fullSubdiff_iff_qSubgradient` proves, in both directions, that this
translated convex subgradient is exactly the global quadratic-support
inequality used elsewhere in the development.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-! ## Convexification and its translated convex subgradient -/

/-- The quadratic convexification appearing in the definition of
`ρ`-weak convexity. -/
def convexification {M N : Nat} (ρ : ℝ) (f : BlockVec M N → ℝ) :
    BlockVec M N → ℝ :=
  fun x => f x + ρ / 2 * blockSq x

/-- The global support-inequality definition of a convex subgradient.
For a convex finite-valued function this is its Fenchel subdifferential. -/
def ConvexSubgradient {M N : Nat} (h : BlockVec M N → ℝ)
    (z p : BlockVec M N) : Prop :=
  ∀ x, h z + blockDot p (x - z) ≤ h x

/-- The full subdifferential of a `ρ`-weakly convex function, represented as
the convex subdifferential of its convexification translated back by `ρ z`.

The accompanying predicate `WeaklyConvex ρ f` certifies that the function
inside `ConvexSubgradient` is genuinely convex. -/
def FullSubgradient {M N : Nat} (ρ : ℝ) (f : BlockVec M N → ℝ)
    (z g : BlockVec M N) : Prop :=
  ConvexSubgradient (convexification ρ f) z (g + ρ • z)

/-- Set-valued form of `FullSubgradient`, suitable for the paper's full-set
oracle. -/
def fullSubdiff {M N : Nat} (ρ : ℝ) (f : BlockVec M N → ℝ)
    (z : BlockVec M N) : Set (BlockVec M N) :=
  {g | FullSubgradient ρ f z g}

theorem weaklyConvex_iff_convex_convexification {M N : Nat}
    {ρ : ℝ} {f : BlockVec M N → ℝ} :
    WeaklyConvex ρ f ↔ ConvexOn ℝ Set.univ (convexification ρ f) := by
  rfl

theorem blockDot_add_left {M N : Nat} (a b d : BlockVec M N) :
    blockDot (a + b) d = blockDot a d + blockDot b d := by
  unfold blockDot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem blockDot_smul_left' {M N : Nat} (ρ : ℝ)
    (z d : BlockVec M N) :
    blockDot (ρ • z) d = ρ * blockDot z d := by
  exact blockDot_smul_left ρ z d

/-- Polarization identity in the exact nested-Pi Euclidean model. -/
theorem blockSq_eq_at_add_displacement {M N : Nat}
    (x z : BlockVec M N) :
    blockSq x = blockSq z + 2 * blockDot z (x - z) + blockSq (x - z) := by
  have h := blockSq_three_point x (0 : BlockVec M N) z
  simp only [sub_zero] at h
  rw [blockDot_comm (x - z) z] at h
  calc
    blockSq x = blockSq (x - z) + blockSq z +
        2 * blockDot z (x - z) := h
    _ = blockSq z + 2 * blockDot z (x - z) + blockSq (x - z) := by ring

/-- The translated convex support inequality and the quadratic support
inequality are exactly equivalent.  No convexity hypothesis is needed for
this algebraic equivalence; `WeaklyConvex ρ f` supplies the semantic reason
for calling the left side a full subdifferential. -/
theorem fullSubgradient_iff_qSubgradient {M N : Nat}
    (ρ : ℝ) (f : BlockVec M N → ℝ) (z g : BlockVec M N) :
    FullSubgradient ρ f z g ↔ QSubgradient (ρ / 2) f z g := by
  constructor
  · intro hg x
    have h := hg x
    unfold ConvexSubgradient convexification at h
    rw [blockDot_add_left, blockDot_smul_left'] at h
    rw [blockSq_eq_at_add_displacement x z] at h
    nlinarith
  · intro hg x
    have h := hg x
    unfold convexification
    rw [blockDot_add_left, blockDot_smul_left']
    rw [blockSq_eq_at_add_displacement x z]
    nlinarith

theorem mem_fullSubdiff_iff_qSubgradient {M N : Nat}
    (ρ : ℝ) (f : BlockVec M N → ℝ) (z g : BlockVec M N) :
    g ∈ fullSubdiff ρ f z ↔ QSubgradient (ρ / 2) f z g := by
  exact fullSubgradient_iff_qSubgradient ρ f z g

theorem fullSubdiff_eq_qSubdiff {M N : Nat}
    (ρ : ℝ) (f : BlockVec M N → ℝ) (z : BlockVec M N) :
    fullSubdiff ρ f z = qSubdiff (ρ / 2) f z := by
  ext g
  exact mem_fullSubdiff_iff_qSubgradient ρ f z g

/-! ## One-block support subgradients for the tilted max-affine function -/

/-- Inner product on a single block. -/
def vecDot {N : Nat} (x y : Fin N → ℝ) : ℝ :=
  ∑ j, x j * y j

/-- Squared Euclidean norm on a single block. -/
def vecSq {N : Nat} (x : Fin N → ℝ) : ℝ :=
  ∑ j, (x j) ^ 2

/-- Ordinary global convex support subgradient on one block. -/
def VecConvexSubgradient {N : Nat} (f : (Fin N → ℝ) → ℝ)
    (u g : Fin N → ℝ) : Prop :=
  ∀ v, f u + vecDot g (v - u) ≤ f v

/-- Quadratic-support form on one block. -/
def VecQSubgradient {N : Nat} (c : ℝ) (f : (Fin N → ℝ) → ℝ)
    (u g : Fin N → ℝ) : Prop :=
  ∀ v, f u + vecDot g (v - u) - c * vecSq (v - u) ≤ f v

theorem vecQSubgradient_zero_iff {N : Nat} (f : (Fin N → ℝ) → ℝ)
    (u g : Fin N → ℝ) :
    VecQSubgradient 0 f u g ↔ VecConvexSubgradient f u g := by
  simp [VecQSubgradient, VecConvexSubgradient]

/-- Every facet is affine with the displayed slope. -/
theorem facetValue_affine {N : Nat} (u v : Fin N → ℝ)
    (s : FacetIndex N) :
    facetValue v s = facetValue u s + vecDot (facetSlope s) (v - u) := by
  cases s with
  | none => simp [facetValue, facetSlope, vecDot]
  | some j =>
      simp [facetValue, facetSlope, vecDot]
      ring

/-- The slope of every active facet is a genuine global convex
subgradient of the finite maximum. -/
theorem activeFacet_slope_vecConvexSubgradient {N : Nat}
    (u : Fin N → ℝ) {s : FacetIndex N} (hs : ActiveFacet u s) :
    VecConvexSubgradient phi u (facetSlope s) := by
  intro v
  rw [← hs, ← facetValue_affine u v s]
  exact facetValue_le_phi v s

/-- An explicit convex combination of active facet slopes is a genuine
global support subgradient of `phi`. -/
theorem phiSubgradient_to_vecConvexSubgradient {N : Nat}
    {u g : Fin N → ℝ} (hg : PhiSubgradient u g) :
    VecConvexSubgradient phi u g := by
  obtain ⟨weights, hnonneg, hsum, hactive, hgcoord⟩ := hg
  intro v
  have hfacet : ∀ s : FacetIndex N,
      weights s * (phi u + vecDot (facetSlope s) (v - u)) ≤
        weights s * phi v := by
    intro s
    by_cases hw : weights s = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_left
        (activeFacet_slope_vecConvexSubgradient u (hactive s hw) v)
        (hnonneg s)
  have hsumineq := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hfacet s)
  have hdot : vecDot g (v - u) =
      ∑ s : FacetIndex N, weights s * vecDot (facetSlope s) (v - u) := by
    unfold vecDot
    simp_rw [hgcoord]
    calc
      (∑ i, (∑ s, weights s * facetSlope s i) * (v - u) i) =
          ∑ i, ∑ s, weights s * (facetSlope s i * (v - u) i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = ∑ s, ∑ i, weights s * (facetSlope s i * (v - u) i) := by
            rw [Finset.sum_comm]
      _ = ∑ s, weights s * ∑ i, facetSlope s i * (v - u) i := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
  simp_rw [mul_add] at hsumineq
  have hleft : (∑ s : FacetIndex N, weights s * phi u) = phi u := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hright : (∑ s : FacetIndex N, weights s * phi v) = phi v := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [Finset.sum_add_distrib, hleft, ← hdot, hright] at hsumineq
  exact hsumineq

theorem phiSubgradient_to_vecQSubgradient_zero {N : Nat}
    {u g : Fin N → ℝ} (hg : PhiSubgradient u g) :
    VecQSubgradient 0 phi u g := by
  exact (vecQSubgradient_zero_iff phi u g).2
    (phiSubgradient_to_vecConvexSubgradient hg)

/-! ### Converse: every support subgradient is an active-slope mixture

The converse is proved directly for this particular tilted maximum.  This
avoids postulating a finite-max rule.  Coordinate and uniform translations
recover the signs, support, and total mass of the active-slope weights.
-/

/-- Translate one coordinate of a block. -/
def shiftCoord {N : Nat} (u : Fin N → ℝ) (i : Fin N) (t : ℝ) : Fin N → ℝ :=
  fun j => u j + if j = i then t else 0

/-- Translate every coordinate by the same scalar. -/
def shiftAll {N : Nat} (u : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  fun j => u j + t

@[simp] theorem shiftCoord_same {N : Nat} (u : Fin N → ℝ)
    (i : Fin N) (t : ℝ) : shiftCoord u i t i = u i + t := by
  simp [shiftCoord]

theorem shiftCoord_ne {N : Nat} (u : Fin N → ℝ)
    {i j : Fin N} (hji : j ≠ i) (t : ℝ) :
    shiftCoord u i t j = u j := by
  simp [shiftCoord, hji]

@[simp] theorem facetValue_shiftCoord_same {N : Nat}
    (u : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    facetValue (shiftCoord u i t) (some i) =
      facetValue u (some i) - (N : ℝ) / 8 * t := by
  simp [facetValue, shiftCoord]
  ring

theorem facetValue_shiftCoord_ne {N : Nat}
    (u : Fin N → ℝ) {i j : Fin N} (hji : j ≠ i) (t : ℝ) :
    facetValue (shiftCoord u i t) (some j) = facetValue u (some j) := by
  simp [facetValue, shiftCoord, hji]

@[simp] theorem facetValue_shiftAll {N : Nat}
    (u : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    facetValue (shiftAll u t) (some j) =
      facetValue u (some j) - (N : ℝ) / 8 * t := by
  simp [facetValue, shiftAll]
  ring

theorem vecDot_shiftCoord_sub {N : Nat} (g u : Fin N → ℝ)
    (i : Fin N) (t : ℝ) :
    vecDot g (shiftCoord u i t - u) = g i * t := by
  classical
  unfold vecDot shiftCoord
  simp

theorem vecDot_shiftAll_sub {N : Nat} (g u : Fin N → ℝ) (t : ℝ) :
    vecDot g (shiftAll u t - u) = (∑ i, g i) * t := by
  unfold vecDot shiftAll
  simp only [Pi.sub_apply, add_sub_cancel_left, Finset.sum_mul]

/-- Increasing one coordinate can only decrease its own tilted facet, hence
cannot increase the finite maximum. -/
theorem phi_shiftCoord_le {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) (i : Fin N) {t : ℝ} (ht : 0 ≤ t) :
    phi (shiftCoord u i t) ≤ phi u := by
  unfold phi
  apply Finset.sup'_le Finset.univ_nonempty
  intro s _
  cases s with
  | none =>
      exact phi_nonneg u
  | some j =>
      by_cases hji : j = i
      · subst j
        rw [facetValue_shiftCoord_same]
        have hbase := facetValue_le_phi u (some i)
        have hcoef : 0 ≤ (N : ℝ) / 8 := by positivity
        have hprod : 0 ≤ (N : ℝ) / 8 * t := mul_nonneg hcoef ht
        exact (sub_le_self _ hprod).trans hbase
      · rw [facetValue_shiftCoord_ne u hji t]
        exact facetValue_le_phi u (some j)

/-- Every global support subgradient has nonpositive coordinates. -/
theorem vecConvexSubgradient_phi_coord_nonpos {N : Nat} (hN : 0 < N)
    {u g : Fin N → ℝ} (hg : VecConvexSubgradient phi u g)
    (i : Fin N) : g i ≤ 0 := by
  have hsupp := hg (shiftCoord u i 1)
  rw [vecDot_shiftCoord_sub] at hsupp
  have hmax := phi_shiftCoord_le hN u i (t := 1) (by norm_num)
  nlinarith

/-- If a nonzero facet is inactive, the corresponding coordinate of every
support subgradient vanishes. -/
theorem vecConvexSubgradient_phi_coord_eq_zero_of_inactive {N : Nat}
    (hN : 0 < N) {u g : Fin N → ℝ}
    (hg : VecConvexSubgradient phi u g) (i : Fin N)
    (hi : ¬ ActiveFacet u (some i)) : g i = 0 := by
  have hnonpos := vecConvexSubgradient_phi_coord_nonpos hN hg i
  let δ : ℝ := phi u - facetValue u (some i)
  have hδ : 0 < δ := by
    have hle := facetValue_le_phi u (some i)
    have hne : facetValue u (some i) ≠ phi u := by
      intro heq
      exact hi heq
    dsimp [δ]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  let t : ℝ := -8 * δ / (N : ℝ)
  have ht : t < 0 := by
    change -8 * δ / (N : ℝ) < 0
    apply div_neg_of_neg_of_pos
    · nlinarith
    · exact_mod_cast hN
  have hfacet : facetValue (shiftCoord u i t) (some i) = phi u := by
    rw [facetValue_shiftCoord_same]
    dsimp [t, δ]
    field_simp [ne_of_gt hN]
    ring
  have hphi : phi (shiftCoord u i t) = phi u := by
    apply le_antisymm
    · unfold phi
      apply Finset.sup'_le Finset.univ_nonempty
      intro s _
      cases s with
      | none => exact phi_nonneg u
      | some j =>
          by_cases hji : j = i
          · subst j
            exact hfacet.le
          · rw [facetValue_shiftCoord_ne u hji t]
            exact facetValue_le_phi u (some j)
    · rw [← hfacet]
      exact facetValue_le_phi (shiftCoord u i t) (some i)
  have hsupp := hg (shiftCoord u i t)
  rw [vecDot_shiftCoord_sub, hphi] at hsupp
  have hnonneg : 0 ≤ g i := by
    nlinarith
  exact le_antisymm hnonpos hnonneg

/-- Uniformly shifting all coordinates down by one raises each nonzero
facet by exactly `N/8`, while the zero facet stays fixed. -/
theorem phi_shiftAll_neg_one_le {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) :
    phi (shiftAll u (-1)) ≤ phi u + (N : ℝ) / 8 := by
  unfold phi
  apply Finset.sup'_le Finset.univ_nonempty
  intro s _
  cases s with
  | none =>
      have hphi := phi_nonneg u
      have hN0 : 0 ≤ (N : ℝ) / 8 := by positivity
      change 0 ≤ phi u + (N : ℝ) / 8
      exact add_nonneg hphi hN0
  | some j =>
      have hbase := facetValue_le_phi u (some j)
      calc
        facetValue (shiftAll u (-1)) (some j) =
            facetValue u (some j) + (N : ℝ) / 8 := by
              rw [facetValue_shiftAll]
              ring
        _ ≤ phi u + (N : ℝ) / 8 := by linarith

/-- The total negative coordinate mass is at most the recession slope
`N/8`. -/
theorem vecConvexSubgradient_phi_neg_sum_le {N : Nat} (hN : 0 < N)
    {u g : Fin N → ℝ} (hg : VecConvexSubgradient phi u g) :
    -(∑ i, g i) ≤ (N : ℝ) / 8 := by
  have hsupp := hg (shiftAll u (-1))
  rw [vecDot_shiftAll_sub] at hsupp
  have hmax := phi_shiftAll_neg_one_le hN u
  nlinarith

/-- If the zero facet is inactive, shifting every coordinate by
`8 * phi(u) / N` lowers every nonzero facet by `phi(u)` and makes the maximum
exactly zero. -/
theorem phi_shiftAll_to_zero_of_none_inactive {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) (hnone : ¬ ActiveFacet u (none : FacetIndex N)) :
    phi (shiftAll u (8 * phi u / (N : ℝ))) = 0 := by
  have hphi : 0 < phi u := by
    have h0 := phi_nonneg u
    have hne : phi u ≠ 0 := by
      intro heq
      apply hnone
      exact heq.symm
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  apply le_antisymm
  · unfold phi
    apply Finset.sup'_le Finset.univ_nonempty
    intro s _
    cases s with
    | none => rfl
    | some j =>
        rw [facetValue_shiftAll]
        have hbase := facetValue_le_phi u (some j)
        have hcancel : (N : ℝ) / 8 * (8 * phi u / (N : ℝ)) = phi u := by
          field_simp [ne_of_gt hN]
        change facetValue u (some j) -
            (N : ℝ) / 8 * (8 * phi u / (N : ℝ)) ≤ 0
        rw [hcancel]
        linarith
  · simpa using facetValue_le_phi
      (shiftAll u (8 * phi u / (N : ℝ))) (none : FacetIndex N)

/-- When the zero facet is inactive, the negative coordinate mass saturates
the recession slope. -/
theorem vecConvexSubgradient_phi_sum_le_neg {N : Nat} (hN : 0 < N)
    {u g : Fin N → ℝ} (hg : VecConvexSubgradient phi u g)
    (hnone : ¬ ActiveFacet u (none : FacetIndex N)) :
    (∑ i, g i) ≤ -(N : ℝ) / 8 := by
  have hphi : 0 < phi u := by
    have h0 := phi_nonneg u
    have hne : phi u ≠ 0 := by
      intro heq
      apply hnone
      exact heq.symm
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  let t : ℝ := 8 * phi u / (N : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hsupp := hg (shiftAll u t)
  rw [vecDot_shiftAll_sub] at hsupp
  have hzero : phi (shiftAll u t) = 0 := by
    dsimp [t]
    exact phi_shiftAll_to_zero_of_none_inactive hN u hnone
  rw [hzero] at hsupp
  have hdiv : (∑ i, g i) ≤ -phi u / t := by
    apply (le_div_iff₀ ht).2
    nlinarith
  have hid : -phi u / t = -(N : ℝ) / 8 := by
    dsimp [t]
    field_simp [ne_of_gt hN, ne_of_gt hphi]
  rw [hid] at hdiv
  exact hdiv

/-- Canonical weights reconstructed from a global support subgradient. -/
def phiSupportWeight {N : Nat} (g : Fin N → ℝ) : FacetIndex N → ℝ
  | none => 1 + (8 : ℝ) / (N : ℝ) * ∑ i, g i
  | some i => -((8 : ℝ) / (N : ℝ)) * g i

@[simp] theorem phiSupportWeight_none {N : Nat} (g : Fin N → ℝ) :
    phiSupportWeight g (none : FacetIndex N) =
      1 + (8 : ℝ) / (N : ℝ) * ∑ i, g i := rfl

@[simp] theorem phiSupportWeight_some {N : Nat} (g : Fin N → ℝ)
    (i : Fin N) :
    phiSupportWeight g (some i) = -((8 : ℝ) / (N : ℝ)) * g i := rfl

theorem phiSupportWeight_nonneg {N : Nat} (hN : 0 < N)
    {u g : Fin N → ℝ} (hg : VecConvexSubgradient phi u g)
    (s : FacetIndex N) : 0 ≤ phiSupportWeight g s := by
  cases s with
  | some i =>
      have hi := vecConvexSubgradient_phi_coord_nonpos hN hg i
      have hc : 0 ≤ (8 : ℝ) / (N : ℝ) := by positivity
      change 0 ≤ -((8 : ℝ) / (N : ℝ)) * g i
      rw [show -((8 : ℝ) / (N : ℝ)) * g i =
          ((8 : ℝ) / (N : ℝ)) * (-g i) by ring]
      exact mul_nonneg hc (neg_nonneg.mpr hi)
  | none =>
      have hbound := vecConvexSubgradient_phi_neg_sum_le hN hg
      have hin : 0 ≤ (N : ℝ) / 8 + ∑ i, g i := by linarith
      have hc : 0 ≤ (8 : ℝ) / (N : ℝ) := by positivity
      change 0 ≤ 1 + (8 : ℝ) / (N : ℝ) * ∑ i, g i
      rw [show 1 + (8 : ℝ) / (N : ℝ) * ∑ i, g i =
          (8 : ℝ) / (N : ℝ) * ((N : ℝ) / 8 + ∑ i, g i) by
            field_simp [ne_of_gt hN]]
      exact mul_nonneg hc hin

theorem phiSupportWeight_sum {N : Nat} (_hN : 0 < N)
    (g : Fin N → ℝ) :
    (∑ s : FacetIndex N, phiSupportWeight g s) = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [phiSupportWeight_none, phiSupportWeight_some]
  have hscaled : (∑ i : Fin N, -((8 : ℝ) / (N : ℝ)) * g i) =
      -((8 : ℝ) / (N : ℝ)) * ∑ i, g i := by
    rw [Finset.mul_sum]
  rw [hscaled]
  ring

theorem phiSupportWeight_active {N : Nat} (hN : 0 < N)
    {u g : Fin N → ℝ} (hg : VecConvexSubgradient phi u g)
    (s : FacetIndex N) (hs : phiSupportWeight g s ≠ 0) :
    ActiveFacet u s := by
  cases s with
  | some i =>
      by_contra hi
      have hgi := vecConvexSubgradient_phi_coord_eq_zero_of_inactive hN hg i hi
      exact hs (by simp [hgi])
  | none =>
      by_contra hnone
      have hupper := vecConvexSubgradient_phi_sum_le_neg hN hg hnone
      have hlower := vecConvexSubgradient_phi_neg_sum_le hN hg
      have heq : (∑ i, g i) = -(N : ℝ) / 8 := by linarith
      apply hs
      simp [phiSupportWeight, heq]
      field_simp [ne_of_gt hN]
      norm_num

theorem phiSupportWeight_reconstruct {N : Nat} (hN : 0 < N)
    (g : Fin N → ℝ) (i : Fin N) :
    g i = ∑ s : FacetIndex N, phiSupportWeight g s * facetSlope s i := by
  classical
  simp [phiSupportWeight, facetSlope]
  field_simp [ne_of_gt hN]

/-- Exact finite-max rule for the manuscript's tilted block.  Both
directions are proved: `PhiSubgradient` is neither an assumption nor merely
an inclusion model. -/
theorem phiSubgradient_iff_vecConvexSubgradient {N : Nat} (hN : 0 < N)
    (u g : Fin N → ℝ) :
    PhiSubgradient u g ↔ VecConvexSubgradient phi u g := by
  constructor
  · exact phiSubgradient_to_vecConvexSubgradient
  · intro hg
    refine ⟨phiSupportWeight g, ?_, ?_, ?_, ?_⟩
    · exact phiSupportWeight_nonneg hN hg
    · exact phiSupportWeight_sum hN g
    · exact phiSupportWeight_active hN hg
    · exact phiSupportWeight_reconstruct hN g

theorem phiSubgradient_iff_vecQSubgradient_zero {N : Nat} (hN : 0 < N)
    (u g : Fin N → ℝ) :
    PhiSubgradient u g ↔ VecQSubgradient 0 phi u g := by
  rw [vecQSubgradient_zero_iff]
  exact phiSubgradient_iff_vecConvexSubgradient hN u g

/-! ## Uniqueness of the positive-activation outer maximizer -/

/-- At a positive activation norm, the canonical positive-part weight is
the *unique* feasible maximizer of the outer support problem.  This is the
unique-active ingredient needed by the hard-function max rule. -/
theorem feasibleOuterWeight_eq_canonical_of_dot_eq {M : Nat}
    {s w : Fin M → ℝ} (hpos : 0 < positiveNorm s)
    (hw : FeasibleOuterWeight w)
    (hmax : outerDot w s = positiveNorm s) :
    w = canonicalOuterWeight s := by
  let p : Fin M → ℝ := fun m => max (s m) 0
  have hterm (m : Fin M) : w m * s m ≤ w m * p m := by
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1 m)
  have houter_le : outerDot w s ≤ ∑ m, w m * p m := by
    unfold outerDot
    exact Finset.sum_le_sum fun m _ => hterm m
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin M)) w p
  have hwsum0 : 0 ≤ ∑ m, (w m) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hpsum0 : 0 ≤ ∑ m, (p m) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hwsqrt_sq := Real.sq_sqrt hwsum0
  have hwsqrt_le : Real.sqrt (∑ m, (w m) ^ 2) ≤ 1 := by
    have hwsqrt0 := Real.sqrt_nonneg (∑ m, (w m) ^ 2)
    nlinarith [hw.2]
  have hpsqrt : Real.sqrt (∑ m, (p m) ^ 2) = positiveNorm s := rfl
  have hsum_le : (∑ m, w m * p m) ≤ positiveNorm s := by
    calc
      (∑ m, w m * p m) ≤
          Real.sqrt (∑ m, (w m) ^ 2) *
            Real.sqrt (∑ m, (p m) ^ 2) := hcs
      _ ≤ Real.sqrt (∑ m, (p m) ^ 2) := by
        exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hwsqrt_le
      _ = positiveNorm s := hpsqrt
  have hwp : (∑ m, w m * p m) = positiveNorm s := by
    apply le_antisymm hsum_le
    rw [← hmax]
    exact houter_le
  have hdotCanonical : outerDot w (canonicalOuterWeight s) = 1 := by
    unfold outerDot canonicalOuterWeight
    calc
      (∑ m, w m * (max (s m) 0 / positiveNorm s)) =
          (∑ m, w m * p m) / positiveNorm s := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro m _
            dsimp [p]
            ring
      _ = 1 := by rw [hwp]; exact div_self hpos.ne'
  have hcanonicalSq := canonicalOuterWeight_sq_sum hpos
  have hdistExpand :
      (∑ m, (w m - canonicalOuterWeight s m) ^ 2) =
        (∑ m, (w m) ^ 2) +
          (∑ m, (canonicalOuterWeight s m) ^ 2) -
            2 * outerDot w (canonicalOuterWeight s) := by
    unfold outerDot
    calc
      (∑ m, (w m - canonicalOuterWeight s m) ^ 2) =
          ∑ m, ((w m) ^ 2 + (canonicalOuterWeight s m) ^ 2 -
            2 * (w m * canonicalOuterWeight s m)) := by
              apply Finset.sum_congr rfl
              intro m _
              ring
      _ = (∑ m, ((w m) ^ 2 + (canonicalOuterWeight s m) ^ 2)) -
          ∑ m, 2 * (w m * canonicalOuterWeight s m) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ m, (w m) ^ 2) +
          (∑ m, (canonicalOuterWeight s m) ^ 2) -
            2 * ∑ m, w m * canonicalOuterWeight s m := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hdistNonpos :
      (∑ m, (w m - canonicalOuterWeight s m) ^ 2) ≤ 0 := by
    rw [hdistExpand, hcanonicalSq, hdotCanonical]
    linarith [hw.2]
  have hdist : (∑ m, (w m - canonicalOuterWeight s m) ^ 2) = 0 := by
    apply le_antisymm hdistNonpos
    exact Finset.sum_nonneg fun m _ => sq_nonneg _
  funext m
  have hsingle : (w m - canonicalOuterWeight s m) ^ 2 ≤
      ∑ i, (w i - canonicalOuterWeight s i) ^ 2 :=
    Finset.single_le_sum
      (fun i _ => sq_nonneg (w i - canonicalOuterWeight s i))
      (Finset.mem_univ m)
  rw [hdist] at hsingle
  nlinarith [sq_nonneg (w m - canonicalOuterWeight s m)]

/-! ## Descent support for the smooth progress carrier -/

/-- Convexification of `-q` at the sharp constant supplied by
`Lip(q') ≤ 6`. -/
def upperQConvexification (t : ℝ) : ℝ := -q t + 3 * t ^ 2

/-- Its represented derivative. -/
def upperQConvexificationPrime (t : ℝ) : ℝ := -qPrime t + 6 * t

theorem hasDerivAt_upperQConvexification (t : ℝ) :
    HasDerivAt upperQConvexification (upperQConvexificationPrime t) t := by
  have hq := (hasDerivAt_q t).neg
  have hs := ((hasDerivAt_id t).pow 2).const_mul 3
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at hs
  unfold upperQConvexification upperQConvexificationPrime
  exact (hq.add hs).congr_deriv (by ring)

theorem differentiable_upperQConvexification :
    Differentiable ℝ upperQConvexification :=
  fun t => (hasDerivAt_upperQConvexification t).differentiableAt

theorem deriv_upperQConvexification (t : ℝ) :
    deriv upperQConvexification t = upperQConvexificationPrime t :=
  (hasDerivAt_upperQConvexification t).deriv

theorem upperQConvexificationPrime_monotone :
    Monotone upperQConvexificationPrime := by
  intro a b hab
  have hlip := qPrime_abs_sub_le a b
  have habs : |a - b| = b - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  rw [habs] at hlip
  have hdiff : qPrime b - qPrime a ≤ 6 * (b - a) := by
    calc
      qPrime b - qPrime a ≤ |qPrime b - qPrime a| := le_abs_self _
      _ = |qPrime a - qPrime b| := abs_sub_comm _ _
      _ ≤ 6 * (b - a) := hlip
  unfold upperQConvexificationPrime
  linarith

theorem upperQConvexification_convex :
    ConvexOn ℝ Set.univ upperQConvexification := by
  apply Monotone.convexOn_univ_of_deriv differentiable_upperQConvexification
  intro a b hab
  rw [deriv_upperQConvexification, deriv_upperQConvexification]
  exact upperQConvexificationPrime_monotone hab

/-- Global support inequality for the differentiable convexification of
`-q`. -/
theorem upperQConvexification_support (a b : ℝ) :
    upperQConvexification a + upperQConvexificationPrime a * (b - a) ≤
      upperQConvexification b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hslope := upperQConvexification_convex.le_slope_of_hasDerivAt
      (Set.mem_univ a) (Set.mem_univ b) hab
      (hasDerivAt_upperQConvexification a)
    rw [slope_def_field] at hslope
    rw [le_div_iff₀ (sub_pos.mpr hab)] at hslope
    linarith
  · subst b
    simp
  · have hslope := upperQConvexification_convex.slope_le_of_hasDerivAt
      (Set.mem_univ b) (Set.mem_univ a) hab
      (hasDerivAt_upperQConvexification a)
    rw [slope_def_field] at hslope
    rw [div_le_iff₀ (sub_pos.mpr hab)] at hslope
    linarith

/-- Sharp scalar descent lemma obtained from `Lip(q') ≤ 6`. -/
theorem q_descent (a b : ℝ) :
    q b ≤ q a + qPrime a * (b - a) + 3 * (b - a) ^ 2 := by
  have h := upperQConvexification_support a b
  unfold upperQConvexification upperQConvexificationPrime at h
  nlinarith [sq_nonneg (b - a)]

/-- The progress carrier satisfies the exact blockwise descent inequality
used in the weak-convexity calculation. -/
theorem psi_descent {N : Nat} (hN : 0 < N) (u v : Fin N → ℝ) :
    psi v ≤ psi u + vecDot (psiGrad u) (v - u) +
      (3 * (N : ℝ) / 16) * vecSq (v - u) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoord (j : Fin N) :
      q ((N : ℝ) * v j / 4) ≤
        q ((N : ℝ) * u j / 4) +
          (N : ℝ) * psiGrad u j * (v j - u j) +
            (3 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2 := by
    have hq := q_descent ((N : ℝ) * u j / 4) ((N : ℝ) * v j / 4)
    unfold psiGrad
    nlinarith
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hcoord j)
  have hlinear :
      (∑ j, (N : ℝ) * psiGrad u j * (v j - u j)) =
        (N : ℝ) * vecDot (psiGrad u) (v - u) := by
    unfold vecDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.sub_apply]
    ring
  have hquadratic :
      (∑ j, (3 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2) =
        (3 * (N : ℝ) ^ 2 / 16) * vecSq (v - u) := by
    unfold vecSq
    rw [Finset.mul_sum]
    rfl
  unfold psi
  rw [div_le_iff₀ hNreal]
  calc
    (∑ j, q ((N : ℝ) * v j / 4)) ≤
        ∑ j, (q ((N : ℝ) * u j / 4) +
          (N : ℝ) * psiGrad u j * (v j - u j) +
            (3 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2) := hsum
    _ = (N : ℝ) *
        ((∑ j, q ((N : ℝ) * u j / 4)) / (N : ℝ) +
          vecDot (psiGrad u) (v - u) +
            (3 * (N : ℝ) / 16) * vecSq (v - u)) := by
      simp only [Finset.sum_add_distrib]
      rw [hlinear, hquadratic]
      field_simp [ne_of_gt hN]
    _ = ((∑ j, q ((N : ℝ) * u j / 4)) / (N : ℝ) +
          vecDot (psiGrad u) (v - u) +
            (3 * (N : ℝ) / 16) * vecSq (v - u)) * (N : ℝ) := by ring

/-- A (deliberately loose) reverse descent estimate.  It follows from the
upper descent lemma and the global Lipschitz bound on `qPrime`; sharpness is
irrelevant here, since only a quadratic remainder must vanish on segments. -/
theorem q_lower_descent (a b : ℝ) :
    q a + qPrime a * (b - a) - 9 * (b - a) ^ 2 ≤ q b := by
  have hupper := q_descent b a
  by_cases hd : 0 ≤ b - a
  · have hderiv : qPrime a - qPrime b ≤ 6 * (b - a) := by
      calc
        qPrime a - qPrime b ≤ |qPrime a - qPrime b| := le_abs_self _
        _ ≤ 6 * |a - b| := qPrime_abs_sub_le a b
        _ = 6 * (b - a) := by
          rw [abs_sub_comm, abs_of_nonneg hd]
    have hmul := mul_le_mul_of_nonneg_right hderiv hd
    nlinarith
  · have hdle : b - a ≤ 0 := le_of_not_ge hd
    have hderiv : qPrime b - qPrime a ≤ -6 * (b - a) := by
      calc
        qPrime b - qPrime a ≤ |qPrime b - qPrime a| := le_abs_self _
        _ ≤ 6 * |b - a| := qPrime_abs_sub_le b a
        _ = -6 * (b - a) := by rw [abs_of_nonpos hdle]; ring
    have hmul := mul_le_mul_of_nonpos_right hderiv hdle
    nlinarith

/-- Two-sided first-order control of the progress carrier.  This lower model
is the estimate needed to upper-bound the negative progress term in a fixed
activation branch. -/
theorem psi_lower_descent {N : Nat} (hN : 0 < N)
    (u v : Fin N → ℝ) :
    psi u + vecDot (psiGrad u) (v - u) -
        (9 * (N : ℝ) / 16) * vecSq (v - u) ≤ psi v := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoord (j : Fin N) :
      q ((N : ℝ) * u j / 4) +
          (N : ℝ) * psiGrad u j * (v j - u j) -
            (9 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2 ≤
        q ((N : ℝ) * v j / 4) := by
    have hq := q_lower_descent
      ((N : ℝ) * u j / 4) ((N : ℝ) * v j / 4)
    unfold psiGrad
    nlinarith
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hcoord j)
  have hlinear :
      (∑ j, (N : ℝ) * psiGrad u j * (v j - u j)) =
        (N : ℝ) * vecDot (psiGrad u) (v - u) := by
    unfold vecDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.sub_apply]
    ring
  have hquadratic :
      (∑ j, (9 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2) =
        (9 * (N : ℝ) ^ 2 / 16) * vecSq (v - u) := by
    unfold vecSq
    rw [Finset.mul_sum]
    rfl
  unfold psi
  rw [le_div_iff₀ hNreal]
  calc
    ((∑ j, q ((N : ℝ) * u j / 4)) / (N : ℝ) +
          vecDot (psiGrad u) (v - u) -
            (9 * (N : ℝ) / 16) * vecSq (v - u)) * (N : ℝ) =
        ∑ j, (q ((N : ℝ) * u j / 4) +
          (N : ℝ) * psiGrad u j * (v j - u j) -
            (9 * (N : ℝ) ^ 2 / 16) * (v j - u j) ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hlinear, hquadratic]
      field_simp [ne_of_gt hNreal]
    _ ≤ ∑ j, q ((N : ℝ) * v j / 4) := hsum

/-! ## Euclidean control of the phase-score map -/

theorem vecSq_block_le_blockSq {M N : Nat} (d : BlockVec M N)
    (m : Fin M) : vecSq (d m) ≤ blockSq d := by
  unfold vecSq blockSq
  exact Finset.single_le_sum
    (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (d i j))
    (Finset.mem_univ m)

theorem phi_sub_sq_le_blockSq {M N : Nat} (hN : 0 < N)
    (x y : BlockVec M N) (m : Fin M) :
    (phi (x m) - phi (y m)) ^ 2 ≤
      ((N : ℝ) ^ 2 / 64) * blockSq (x - y) := by
  have hphi := phi_sub_sq_le hN (x m) (y m)
  have hblock := vecSq_block_le_blockSq (x - y) m
  calc
    (phi (x m) - phi (y m)) ^ 2 ≤
        ((N : ℝ) ^ 2 / 64) * vecSq ((x - y) m) := by
      simpa [vecSq, WeaklyConvexLowerBound.Foundation.vecSq,
        Pi.sub_apply] using hphi
    _ ≤ ((N : ℝ) ^ 2 / 64) * blockSq (x - y) :=
      mul_le_mul_of_nonneg_left hblock (by positivity)

theorem previousProgress_sub_sq_le_blockSq {M N : Nat} (hN : 0 < N)
    (x y : BlockVec M N) (m : Fin M) :
    (previousProgress x m - previousProgress y m) ^ 2 ≤
      (9 * (N : ℝ) / 64) * blockSq (x - y) := by
  by_cases hm : m.1 = 0
  · have hnon : 0 ≤ (9 * (N : ℝ) / 64) * blockSq (x - y) :=
      mul_nonneg (by positivity) (blockSq_nonneg _)
    simpa [previousProgress, hm] using hnon
  · let p : Fin M := ⟨m.1 - 1, by omega⟩
    have hpsi := psi_sub_sq_le hN (x p) (y p)
    have hblock := vecSq_block_le_blockSq (x - y) p
    calc
      (previousProgress x m - previousProgress y m) ^ 2 =
          (psi (x p) - psi (y p)) ^ 2 := by simp [previousProgress, hm, p]
      _ ≤ (9 * (N : ℝ) / 64) * vecSq ((x - y) p) := by
        simpa [vecSq, WeaklyConvexLowerBound.Foundation.vecSq,
          Pi.sub_apply] using hpsi
      _ ≤ (9 * (N : ℝ) / 64) * blockSq (x - y) :=
        mul_le_mul_of_nonneg_left hblock (by positivity)

theorem sigmaScore_sub_sq_le_blockSq {M N : Nat} (hN : 0 < N)
    (x y : BlockVec M N) (m : Fin M) :
    (sigmaScore x m - sigmaScore y m) ^ 2 ≤
      ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) * blockSq (x - y) := by
  let a := phi (x m) - phi (y m)
  let b := previousProgress x m - previousProgress y m
  have ha := phi_sub_sq_le_blockSq hN x y m
  have hb := previousProgress_sub_sq_le_blockSq hN x y m
  have hab : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hscore : sigmaScore x m - sigmaScore y m = a + b := by
    simp [sigmaScore, a, b]
    ring
  rw [hscore]
  calc
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := hab
    _ ≤ 2 * (((N : ℝ) ^ 2 / 64) * blockSq (x - y)) +
        2 * ((9 * (N : ℝ) / 64) * blockSq (x - y)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) *
        blockSq (x - y) := by ring

theorem sigmaScore_sub_sq_sum_le {M N : Nat} (hN : 0 < N)
    (x y : BlockVec M N) :
    (∑ m, (sigmaScore x m - sigmaScore y m) ^ 2) ≤
      (M : ℝ) * ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) *
        blockSq (x - y) := by
  calc
    (∑ m, (sigmaScore x m - sigmaScore y m) ^ 2) ≤
        ∑ _m : Fin M,
          (((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) *
            blockSq (x - y)) :=
      Finset.sum_le_sum fun m _ ↦ sigmaScore_sub_sq_le_blockSq hN x y m
    _ = (M : ℝ) * ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32) *
        blockSq (x - y) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-! ## A quadratic upper model for the positive-part norm -/

private theorem max_sq_upper_model (a b : ℝ) :
    (max b 0) ^ 2 ≤ (max a 0) ^ 2 +
      2 * max a 0 * (b - a) + (b - a) ^ 2 := by
  by_cases ha : a ≤ 0
  · rw [max_eq_right ha]
    by_cases hb : b ≤ 0
    · rw [max_eq_right hb]
      nlinarith [sq_nonneg (b - a)]
    · rw [max_eq_left (le_of_not_ge hb)]
      nlinarith [sq_nonneg (b - a)]
  · rw [max_eq_left (le_of_not_ge ha)]
    by_cases hb : b ≤ 0
    · rw [max_eq_right hb]
      nlinarith [sq_nonneg b]
    · rw [max_eq_left (le_of_not_ge hb)]
      nlinarith

/-- Squared first-order upper model before applying the square root. -/
theorem positiveNorm_sq_upper_model {M : Nat} (s t : Fin M → ℝ)
    (hpos : 0 < positiveNorm s) :
    positiveNorm t ^ 2 ≤ positiveNorm s ^ 2 +
      2 * positiveNorm s *
        outerDot (canonicalOuterWeight s) (t - s) +
          (∑ m, (t m - s m) ^ 2) := by
  have hs0 : 0 ≤ ∑ m : Fin M, (max (s m) 0) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have ht0 : 0 ≤ ∑ m : Fin M, (max (t m) 0) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hsSq : positiveNorm s ^ 2 = ∑ m, (max (s m) 0) ^ 2 := by
    exact Real.sq_sqrt hs0
  have htSq : positiveNorm t ^ 2 = ∑ m, (max (t m) 0) ^ 2 := by
    exact Real.sq_sqrt ht0
  have hdot : positiveNorm s *
      outerDot (canonicalOuterWeight s) (t - s) =
      ∑ m, max (s m) 0 * (t m - s m) := by
    unfold outerDot canonicalOuterWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    simp only [Pi.sub_apply]
    field_simp [hpos.ne']
  rw [htSq, hsSq]
  rw [mul_assoc, hdot]
  calc
    (∑ m, (max (t m) 0) ^ 2) ≤
        ∑ m, ((max (s m) 0) ^ 2 +
          2 * max (s m) 0 * (t m - s m) + (t m - s m) ^ 2) := by
            exact Finset.sum_le_sum fun m _ => max_sq_upper_model (s m) (t m)
    _ = (∑ m, (max (s m) 0) ^ 2) +
        2 * ∑ m, max (s m) 0 * (t m - s m) +
          ∑ m, (t m - s m) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            congr 2
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            ring

/-- Local quadratic upper estimate for the positive-part norm.  The explicit
nonnegativity premise is automatic for sufficiently small perturbations and
keeps the statement free of hidden neighborhood choices. -/
theorem positiveNorm_quadratic_upper {M : Nat} {s t : Fin M → ℝ}
    (hpos : 0 < positiveNorm s)
    (hrhs : 0 ≤ positiveNorm s +
      outerDot (canonicalOuterWeight s) (t - s) +
        (∑ m, (t m - s m) ^ 2) / (2 * positiveNorm s)) :
    positiveNorm t ≤ positiveNorm s +
      outerDot (canonicalOuterWeight s) (t - s) +
        (∑ m, (t m - s m) ^ 2) / (2 * positiveNorm s) := by
  let A := outerDot (canonicalOuterWeight s) (t - s)
  let B := ∑ m, (t m - s m) ^ 2
  have hmodel := positiveNorm_sq_upper_model s t hpos
  have hden : 0 < 2 * positiveNorm s := by positivity
  have hsquare : positiveNorm s ^ 2 + 2 * positiveNorm s * A + B ≤
      (positiveNorm s + A + B / (2 * positiveNorm s)) ^ 2 := by
    have heq : (positiveNorm s + A + B / (2 * positiveNorm s)) ^ 2 =
        positiveNorm s ^ 2 + 2 * positiveNorm s * A + B +
          (A + B / (2 * positiveNorm s)) ^ 2 := by
      field_simp [hpos.ne']
      ring
    rw [heq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  dsimp [A, B] at hsquare
  have hsq := hmodel.trans hsquare
  nlinarith [positiveNorm_nonneg t]

/-- Cauchy--Schwarz for the canonical positive-part direction.  At a
positive base point that direction has Euclidean norm one. -/
theorem canonicalOuterWeight_dot_sub_sq_le {M : Nat}
    {s t : Fin M → ℝ} (hpos : 0 < positiveNorm s) :
    (outerDot (canonicalOuterWeight s) (t - s)) ^ 2 ≤
      ∑ m, (t m - s m) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin M))
    (r := fun m ↦ canonicalOuterWeight s m * (t m - s m))
    (f := fun m ↦ (canonicalOuterWeight s m) ^ 2)
    (g := fun m ↦ (t m - s m) ^ 2)
    (fun m _ ↦ sq_nonneg _) (fun m _ ↦ sq_nonneg _)
    (fun m _ ↦ by rw [mul_pow])
  unfold outerDot
  simp only [Pi.sub_apply]
  rw [canonicalOuterWeight_sq_sum hpos, one_mul] at hcs
  exact hcs

/-- The nonnegativity side condition in `positiveNorm_quadratic_upper` is in
fact automatic.  This global form is the convenient contact estimate used
to identify the unique active branch at positive activation. -/
theorem positiveNorm_quadratic_upper_global {M : Nat}
    {s t : Fin M → ℝ} (hpos : 0 < positiveNorm s) :
    positiveNorm t ≤ positiveNorm s +
      outerDot (canonicalOuterWeight s) (t - s) +
        (∑ m, (t m - s m) ^ 2) / (2 * positiveNorm s) := by
  apply positiveNorm_quadratic_upper hpos
  let A := outerDot (canonicalOuterWeight s) (t - s)
  let B := ∑ m, (t m - s m) ^ 2
  have hA2 : A ^ 2 ≤ B := by
    simpa [A, B] using canonicalOuterWeight_dot_sub_sq_le (s := s) (t := t) hpos
  have hden : 0 < 2 * positiveNorm s := by positivity
  have hdiv : A ^ 2 / (2 * positiveNorm s) ≤
      B / (2 * positiveNorm s) := by
    exact (div_le_div_iff_of_pos_right hden).2 hA2
  have hbase : 0 ≤ positiveNorm s + A +
      A ^ 2 / (2 * positiveNorm s) := by
    have heq : positiveNorm s + A + A ^ 2 / (2 * positiveNorm s) =
        ((positiveNorm s + A) ^ 2 + positiveNorm s ^ 2) /
          (2 * positiveNorm s) := by
      field_simp [hpos.ne']
      ring
    rw [heq]
    exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le
  dsimp [A, B] at hdiv hbase ⊢
  linarith

theorem outerDot_sub_right {M : Nat} (w a b : Fin M → ℝ) :
    outerDot w (a - b) = outerDot w a - outerDot w b := by
  unfold outerDot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- At positive activation, the hard value has second-order contact with the
canonical fixed-weight branch. -/
theorem hardValue_sub_le_canonicalBranch_sub_add {M N : Nat}
    (hN : 0 < N) {z : BlockVec M N} (hR : 0 < activationNorm z)
    (y : BlockVec M N) :
    hardValue y - hardValue z ≤
      activationBranch (canonicalOuterWeight (sigmaScore z)) y -
        activationBranch (canonicalOuterWeight (sigmaScore z)) z +
      (2 / (N : ℝ)) *
        ((∑ m, (sigmaScore y m - sigmaScore z m) ^ 2) /
          (2 * activationNorm z)) := by
  have hpos : 0 < positiveNorm (sigmaScore z) := by
    simpa [← activationNorm_eq_positiveNorm] using hR
  have hup := positiveNorm_quadratic_upper_global
    (s := sigmaScore z) (t := sigmaScore y) hpos
  change activationNorm y ≤ activationNorm z +
      outerDot (canonicalOuterWeight (sigmaScore z))
        (sigmaScore y - sigmaScore z) +
      (∑ m, (sigmaScore y m - sigmaScore z m) ^ 2) /
        (2 * activationNorm z) at hup
  rw [outerDot_sub_right] at hup
  have hscale : 0 ≤ 2 / (N : ℝ) := by positivity
  let Q := (∑ m, (sigmaScore y m - sigmaScore z m) ^ 2) /
    (2 * activationNorm z)
  calc
    hardValue y - hardValue z =
        (2 / (N : ℝ)) *
          ((activationNorm y - activationNorm z) -
            ((∑ m, psi (y m)) - ∑ m, psi (z m))) := by
      unfold hardValue
      ring
    _ ≤ (2 / (N : ℝ)) *
        ((outerDot (canonicalOuterWeight (sigmaScore z)) (sigmaScore y) -
            outerDot (canonicalOuterWeight (sigmaScore z)) (sigmaScore z) + Q) -
          ((∑ m, psi (y m)) - ∑ m, psi (z m))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      dsimp [Q]
      linarith
    _ = activationBranch (canonicalOuterWeight (sigmaScore z)) y -
        activationBranch (canonicalOuterWeight (sigmaScore z)) z +
          (2 / (N : ℝ)) * Q := by
      unfold activationBranch
      ring
    _ = _ := by rfl

/-! ## One-block line segments -/

/-- Change a single block along a line, leaving all other blocks fixed. -/
def blockLine {M N : Nat} (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ) : BlockVec M N :=
  z + t • singleBlock m (v - z m)

@[simp] theorem blockLine_same {M N : Nat} (z : BlockVec M N)
    (m : Fin M) (v : Fin N → ℝ) (t : ℝ) :
    blockLine z m v t m = (1 - t) • z m + t • v := by
  classical
  ext j
  simp [blockLine, singleBlock]
  ring

theorem blockLine_other {M N : Nat} (z : BlockVec M N)
    {m i : Fin M} (h : i ≠ m) (v : Fin N → ℝ) (t : ℝ) :
    blockLine z m v t i = z i := by
  classical
  ext j
  simp [blockLine, singleBlock, h]

theorem blockLine_sub {M N : Nat} (z : BlockVec M N)
    (m : Fin M) (v : Fin N → ℝ) (t : ℝ) :
    blockLine z m v t - z = t • singleBlock m (v - z m) := by
  ext i j
  simp [blockLine]

theorem blockLine_same_sub {M N : Nat} (z : BlockVec M N)
    (m : Fin M) (v : Fin N → ℝ) (t : ℝ) :
    blockLine z m v t m - z m = t • (v - z m) := by
  ext j
  simp [blockLine_same]
  ring

theorem vecDot_smul_right_param {N : Nat} (g d : Fin N → ℝ) (t : ℝ) :
    vecDot g (t • d) = t * vecDot g d := by
  unfold vecDot
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vecSq_smul_param {N : Nat} (d : Fin N → ℝ) (t : ℝ) :
    vecSq (t • d) = t ^ 2 * vecSq d := by
  unfold vecSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem blockSq_blockLine_sub {M N : Nat} (z : BlockVec M N)
    (m : Fin M) (v : Fin N → ℝ) (t : ℝ) :
    blockSq (blockLine z m v t - z) = t ^ 2 * vecSq (v - z m) := by
  classical
  rw [blockLine_sub]
  simp [blockSq, singleBlock, vecSq, mul_pow, Finset.mul_sum]

theorem blockDot_blockLine_sub {M N : Nat} (g z : BlockVec M N)
    (m : Fin M) (v : Fin N → ℝ) (t : ℝ) :
    blockDot g (blockLine z m v t - z) =
      t * vecDot (g m) (v - z m) := by
  classical
  rw [blockLine_sub]
  simp [blockDot, vecDot, singleBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem activationBranch_blockLine_sub_eq {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ) :
    activationBranch w (blockLine z m v t) - activationBranch w z =
      (2 / (N : ℝ)) *
        (w m * (phi (blockLine z m v t m) - phi (z m)) -
          netProgressWeight w m *
            (psi (blockLine z m v t m) - psi (z m))) := by
  classical
  rw [activationBranch_sub_eq hM]
  unfold branchFanDifference branchProgressDifference
  have hfan :
      (∑ i, w i * (phi (blockLine z m v t i) - phi (z i))) =
        w m * (phi (blockLine z m v t m) - phi (z m)) := by
    rw [Finset.sum_eq_single m]
    · intro i _ him
      rw [blockLine_other z him v t]
      ring
    · simp
  have hprog :
      (∑ i, netProgressWeight w i *
        (psi (blockLine z m v t i) - psi (z i))) =
        netProgressWeight w m *
          (psi (blockLine z m v t m) - psi (z m)) := by
    rw [Finset.sum_eq_single m]
    · intro i _ him
      rw [blockLine_other z him v t]
      ring
    · simp
  rw [hfan, hprog]
  ring

/-- First-order upper model of a fixed feasible branch on a one-block line. -/
theorem activationBranch_blockLine_upper {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    activationBranch w (blockLine z m v t) - activationBranch w z ≤
      t * (2 / (N : ℝ)) *
        (w m * (phi v - phi (z m)) -
          netProgressWeight w m * vecDot (psiGrad (z m)) (v - z m)) +
      (2 / (N : ℝ)) * netProgressWeight w m *
        (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m) := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hphiConv := phi_convexOn.2
    (Set.mem_univ (z m)) (Set.mem_univ v) h1t ht0
      (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hphiConv
  have hphi : phi (blockLine z m v t m) - phi (z m) ≤
      t * (phi v - phi (z m)) := by
    rw [blockLine_same]
    nlinarith
  have hpsi0 := psi_lower_descent hN (z m) (blockLine z m v t m)
  rw [blockLine_same_sub, vecDot_smul_right_param, vecSq_smul_param] at hpsi0
  have hpsi :
      t * vecDot (psiGrad (z m)) (v - z m) -
          (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m) ≤
        psi (blockLine z m v t m) - psi (z m) := by
    linarith
  have hw0 := hw.1 m
  have ha0 := netProgressWeight_nonneg hw m
  have hfan := mul_le_mul_of_nonneg_left hphi hw0
  have hprog := mul_le_mul_of_nonneg_left hpsi ha0
  have hinner :
      w m * (phi (blockLine z m v t m) - phi (z m)) -
          netProgressWeight w m *
            (psi (blockLine z m v t m) - psi (z m)) ≤
        t * (w m * (phi v - phi (z m)) -
          netProgressWeight w m * vecDot (psiGrad (z m)) (v - z m)) +
        netProgressWeight w m * (9 * (N : ℝ) / 16) *
          t ^ 2 * vecSq (v - z m) := by
    nlinarith
  rw [activationBranch_blockLine_sub_eq hM]
  have hscale : 0 ≤ 2 / (N : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hinner hscale
  nlinarith

/-! ## Removing a uniform quadratic remainder -/

theorem linear_le_of_segment_quadratic {A B C : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t * A ≤ t * B + C * t ^ 2) :
    A ≤ B := by
  by_contra hAB
  let δ : ℝ := A - B
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr (lt_of_not_ge hAB)
  let D : ℝ := |C| + δ + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith [abs_nonneg C]
  let t : ℝ := δ / (2 * D)
  have hden : 0 < 2 * D := by positivity
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hδ hden
  have ht_one : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hden]
    dsimp [D]
    linarith [abs_nonneg C]
  have hCt : |C| * t ≤ δ / 2 := by
    have hCD : |C| ≤ D := by
      dsimp [D]
      linarith
    have hmul : |C| * δ ≤ D * δ :=
      mul_le_mul_of_nonneg_right hCD hδ.le
    dsimp [t]
    rw [show |C| * (δ / (2 * D)) = (|C| * δ) / (2 * D) by ring]
    rw [div_le_iff₀ hden]
    nlinarith
  have hmain := h t ht ht_one
  have hlinear : t * δ ≤ C * t ^ 2 := by
    dsimp [δ]
    nlinarith
  have hCabs : C * t ^ 2 ≤ |C| * t ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg t)
  have hrem : |C| * t ^ 2 ≤ (δ / 2) * t := by
    simpa [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hCt ht.le
  have : t * δ ≤ (δ / 2) * t := hlinear.trans (hCabs.trans hrem)
  nlinarith

/-- Every sharp quadratic support of the hard function obeys the exact
one-block first-order support inequality of the canonical active branch. -/
theorem qSubgradient_hardValue_block_support {M N : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hR : 0 < activationNorm z)
    (hg : QSubgradient (3 / 8 : ℝ) (@hardValue M N) z g)
    (m : Fin M) (v : Fin N → ℝ) :
    vecDot (g m) (v - z m) ≤
      (2 / (N : ℝ)) *
        (canonicalOuterWeight (sigmaScore z) m * (phi v - phi (z m)) -
          netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
            vecDot (psiGrad (z m)) (v - z m)) := by
  let A := vecDot (g m) (v - z m)
  let B := (2 / (N : ℝ)) *
    (canonicalOuterWeight (sigmaScore z) m * (phi v - phi (z m)) -
      netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
        vecDot (psiGrad (z m)) (v - z m))
  let K := (M : ℝ) *
    ((N : ℝ) ^ 2 / 32 + 9 * (N : ℝ) / 32)
  let V := vecSq (v - z m)
  let a := netProgressWeight (canonicalOuterWeight (sigmaScore z)) m
  let C := (3 / 8 : ℝ) * V +
    (2 / (N : ℝ)) * a * (9 * (N : ℝ) / 16) * V +
    (2 / (N : ℝ)) * (K * V / (2 * activationNorm z))
  apply linear_le_of_segment_quadratic (A := A) (B := B) (C := C)
  intro t ht ht1
  have ht0 : 0 ≤ t := ht.le
  let y := blockLine z m v t
  have hq := hg y
  have hcontact := hardValue_sub_le_canonicalBranch_sub_add
    hA.N_pos hR y
  have hbranch := activationBranch_blockLine_upper
    hA.M_pos hA.N_pos (canonicalOuterWeight_feasible (sigmaScore z))
      z m v t ht0 ht1
  have hscore := sigmaScore_sub_sq_sum_le hA.N_pos y z
  have hysq : blockSq (y - z) = t ^ 2 * V := by
    dsimp [y, V]
    exact blockSq_blockLine_sub z m v t
  rw [hysq] at hscore
  have hden : 0 < 2 * activationNorm z := by positivity
  have hdiv :
      (∑ i, (sigmaScore y i - sigmaScore z i) ^ 2) /
          (2 * activationNorm z) ≤
        K * t ^ 2 * V / (2 * activationNorm z) := by
    apply (div_le_div_iff_of_pos_right hden).2
    dsimp [K] at hscore ⊢
    nlinarith
  have hscale : 0 ≤ 2 / (N : ℝ) := by positivity
  have hrem := mul_le_mul_of_nonneg_left hdiv hscale
  have hydot : blockDot g (y - z) = t * A := by
    dsimp [y, A]
    exact blockDot_blockLine_sub g z m v t
  rw [hydot, hysq] at hq
  have hbranch' :
      activationBranch (canonicalOuterWeight (sigmaScore z)) y -
          activationBranch (canonicalOuterWeight (sigmaScore z)) z ≤
        t * B +
          (2 / (N : ℝ)) *
            netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
              (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m) := by
    dsimp [y]
    calc
      activationBranch (canonicalOuterWeight (sigmaScore z))
            (blockLine z m v t) -
          activationBranch (canonicalOuterWeight (sigmaScore z)) z ≤
        t * (2 / (N : ℝ)) *
            (canonicalOuterWeight (sigmaScore z) m * (phi v - phi (z m)) -
              netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
                vecDot (psiGrad (z m)) (v - z m)) +
          (2 / (N : ℝ)) *
            netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
              (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m) := hbranch
      _ = t * B +
          (2 / (N : ℝ)) *
            netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
              (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m) := by
        dsimp [B]
        ring
  have hq' : t * A ≤ hardValue y - hardValue z +
      (3 / 8 : ℝ) * (t ^ 2 * V) := by
    linarith
  have hcontact' : hardValue y - hardValue z ≤
      activationBranch (canonicalOuterWeight (sigmaScore z)) y -
          activationBranch (canonicalOuterWeight (sigmaScore z)) z +
        (2 / (N : ℝ)) *
          (K * t ^ 2 * V / (2 * activationNorm z)) := by
    calc
      hardValue y - hardValue z ≤
          activationBranch (canonicalOuterWeight (sigmaScore z)) y -
              activationBranch (canonicalOuterWeight (sigmaScore z)) z +
            (2 / (N : ℝ)) *
              ((∑ i, (sigmaScore y i - sigmaScore z i) ^ 2) /
                (2 * activationNorm z)) := hcontact
      _ ≤ activationBranch (canonicalOuterWeight (sigmaScore z)) y -
              activationBranch (canonicalOuterWeight (sigmaScore z)) z +
            (2 / (N : ℝ)) *
              (K * t ^ 2 * V / (2 * activationNorm z)) :=
        add_le_add le_rfl hrem
  have hhard : hardValue y - hardValue z ≤
      (t * B +
        (2 / (N : ℝ)) *
          netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
            (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m)) +
        (2 / (N : ℝ)) *
          (K * t ^ 2 * V / (2 * activationNorm z)) := by
    exact hcontact'.trans (add_le_add hbranch' le_rfl)
  calc
    t * A ≤ hardValue y - hardValue z +
        (3 / 8 : ℝ) * (t ^ 2 * V) := hq'
    _ ≤ ((t * B +
          (2 / (N : ℝ)) *
            netProgressWeight (canonicalOuterWeight (sigmaScore z)) m *
              (9 * (N : ℝ) / 16) * t ^ 2 * vecSq (v - z m)) +
          (2 / (N : ℝ)) *
            (K * t ^ 2 * V / (2 * activationNorm z))) +
        (3 / 8 : ℝ) * (t ^ 2 * V) := add_le_add hhard le_rfl
    _ = t * B + C * t ^ 2 := by
      dsimp [C, K, V, a]
      ring

/-! ## Independence of the chosen weak-convexity modulus -/

def blockSegment {M N : Nat} (z x : BlockVec M N) (t : ℝ) :
    BlockVec M N :=
  (1 - t) • z + t • x

theorem blockSegment_sub_left {M N : Nat} (z x : BlockVec M N) (t : ℝ) :
    blockSegment z x t - z = t • (x - z) := by
  ext m j
  simp [blockSegment]
  ring

theorem blockSq_smul_param {M N : Nat} (t : ℝ) (d : BlockVec M N) :
    blockSq (t • d) = t ^ 2 * blockSq d := by
  unfold blockSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem blockDot_smul_right_param {M N : Nat} (g d : BlockVec M N) (t : ℝ) :
    blockDot g (t • d) = t * blockDot g d := by
  rw [blockDot_comm, blockDot_smul_left, blockDot_comm]

theorem blockSq_segment {M N : Nat} (z x : BlockVec M N) (t : ℝ) :
    blockSq (blockSegment z x t) =
      (1 - t) * blockSq z + t * blockSq x -
        t * (1 - t) * blockSq (x - z) := by
  have hseg : blockSegment z x t = z + t • (x - z) := by
    ext m j
    simp [blockSegment]
    ring
  have hbase := blockSq_eq_at_add_displacement x z
  rw [hseg, blockSq_eq_at_add_displacement]
  have hsub : z + t • (x - z) - z = t • (x - z) := by
    ext m j
    simp
  rw [hsub, blockDot_smul_right_param, blockSq_smul_param]
  rw [hbase]
  ring

/-- Once one quadratic convexification is convex, every global quadratic
support vector tightens to the smallest certified modulus.  Thus the full
subdifferential does not depend on whether the manuscript records the sharp
`3/4` modulus or the looser class modulus `1`. -/
theorem QSubgradient.tighten_of_weaklyConvex {M N : Nat}
    {ρ c : ℝ} {f : BlockVec M N → ℝ} {z g : BlockVec M N}
    (hconv : WeaklyConvex ρ f) (hc : ρ / 2 ≤ c)
    (hg : QSubgradient c f z g) :
    QSubgradient (ρ / 2) f z g := by
  intro x
  let A := f z + blockDot g (x - z) - ρ / 2 * blockSq (x - z)
  let B := f x
  let C := (c - ρ / 2) * blockSq (x - z)
  apply linear_le_of_segment_quadratic (A := A) (B := B) (C := C)
  intro t ht ht1
  have ht0 : 0 ≤ t := ht.le
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let y := blockSegment z x t
  have hq := hg y
  have hcv := hconv.2 (Set.mem_univ z) (Set.mem_univ x)
    h1t ht0 (by ring : (1 - t) + t = 1)
  change f y + ρ / 2 * blockSq y ≤
    (1 - t) • (f z + ρ / 2 * blockSq z) +
      t • (f x + ρ / 2 * blockSq x) at hcv
  have hyz : y - z = t • (x - z) := by
    dsimp [y]
    exact blockSegment_sub_left z x t
  rw [hyz, blockDot_smul_right_param, blockSq_smul_param] at hq
  have hysq := blockSq_segment z x t
  rw [hysq] at hcv
  simp only [smul_eq_mul] at hcv
  dsimp [A, B, C]
  nlinarith

theorem fullSubdiff_one_subset_threeQuarter {M N : Nat}
    (hA : Admissible M N) (z : BlockVec M N) :
    fullSubdiff 1 (@hardValue M N) z ⊆
      fullSubdiff (3 / 4 : ℝ) (@hardValue M N) z := by
  intro g hg
  rw [mem_fullSubdiff_iff_qSubgradient] at hg ⊢
  exact hg.tighten_of_weaklyConvex
    (hardValue_threeQuarter_weaklyConvex hA) (by norm_num)

/-- Exact positive-activation reconstruction of the manuscript's block
formula from a sharp quadratic support vector. -/
noncomputable def qSubgradient_threeEighths_hardFormulaReply {M N : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hR : 0 < activationNorm z)
    (hg : QSubgradient (3 / 8 : ℝ) (@hardValue M N) z g) :
    HardFormulaReply z g := by
  classical
  let w : Fin M → ℝ := canonicalOuterWeight (sigmaScore z)
  let a : Fin M → ℝ := netProgressWeight w
  let u : BlockVec M N := fun m ↦
    if hm : w m = 0 then
      facetSlope (Classical.choose (exists_activeFacet (z m)))
    else
      fun j ↦ ((N : ℝ) / (2 * w m)) * g m j +
        (a m / w m) * psiGrad (z m) j
  have hsupp (m : Fin M) (v : Fin N → ℝ) :
      vecDot (g m) (v - z m) ≤
        (2 / (N : ℝ)) *
          (w m * (phi v - phi (z m)) -
            a m * vecDot (psiGrad (z m)) (v - z m)) := by
    simpa [w, a] using
      qSubgradient_hardValue_block_support hA hR hg m v
  have hu : ∀ m, PhiSubgradient (z m) (u m) := by
    intro m
    by_cases hm : w m = 0
    · simpa [u, hm] using
        activeFacet_slope_is_PhiSubgradient (z m)
          (Classical.choose_spec (exists_activeFacet (z m)))
    · apply (phiSubgradient_iff_vecConvexSubgradient hA.N_pos (z m) (u m)).2
      intro v
      have hs := hsupp m v
      have hw0 : 0 ≤ w m := by
        dsimp [w]
        exact canonicalOuterWeight_nonneg _ m
      have hwpos : 0 < w m := lt_of_le_of_ne hw0 (Ne.symm hm)
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
      have hcoef : 0 < (N : ℝ) / (2 * w m) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hs hcoef.le
      have hcancel :
          ((N : ℝ) / (2 * w m)) *
              ((2 / (N : ℝ)) *
                (w m * (phi v - phi (z m)) -
                  a m * vecDot (psiGrad (z m)) (v - z m))) =
            (phi v - phi (z m)) -
              (a m / w m) * vecDot (psiGrad (z m)) (v - z m) := by
        field_simp [hNreal.ne', hm]
      rw [hcancel] at hmul
      have hdot : vecDot (u m) (v - z m) =
          ((N : ℝ) / (2 * w m)) * vecDot (g m) (v - z m) +
            (a m / w m) * vecDot (psiGrad (z m)) (v - z m) := by
        unfold vecDot
        simp only [u, dif_neg hm, Pi.sub_apply]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        apply congrArg₂ (fun p q : ℝ ↦ p + q)
        · apply Finset.sum_congr rfl
          intro j _
          ring
        · apply Finset.sum_congr rfl
          intro j _
          ring
      change phi (z m) + vecDot (u m) (v - z m) ≤ phi v
      rw [hdot]
      linarith
  have hcanon : ∀ m j, g m j =
      (2 / (N : ℝ)) *
        (w m * u m j - a m * psiGrad (z m) j) := by
    intro m j
    by_cases hm : w m = 0
    · have hp := hsupp m (shiftCoord (z m) j 1)
      have hn := hsupp m (shiftCoord (z m) j (-1))
      rw [vecDot_shiftCoord_sub, vecDot_shiftCoord_sub, hm] at hp hn
      norm_num only [mul_one, one_mul, zero_mul, zero_sub, mul_neg,
        mul_neg_one, neg_mul, neg_neg] at hp hn
      have heq : g m j =
          -(2 / (N : ℝ)) * a m * psiGrad (z m) j := by
        nlinarith
      rw [hm, zero_mul, zero_sub]
      calc
        g m j = -(2 / (N : ℝ)) * a m * psiGrad (z m) j := heq
        _ = (2 / (N : ℝ)) * (-(a m * psiGrad (z m) j)) := by ring
    · have hNreal : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
      simp only [u, dif_neg hm]
      field_simp [hNreal.ne', hm]
      ring
  refine
    { u := u
      u_subgradient := hu
      g_eq := ?_ }
  intro m j
  have h := hcanon m j
  have hw_eq : w = activeWeight z := by
    exact (activeWeight_eq_canonicalOuterWeight z).symm
  have ha_eq : a = netCoefficient z := by
    funext i
    unfold a netProgressWeight netCoefficient
    rw [hw_eq]
    unfold nextOuterWeight nextActiveWeight
    rfl
  rw [hw_eq, ha_eq] at h
  exact h

/-- The full weakly-convex subdifferential at every positive-activation point
is contained in the exact formula set used by the lower-bound oracle. -/
noncomputable def fullSubdiff_one_positive_hardFormulaReply {M N : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hR : 0 < activationNorm z)
    (hg : g ∈ fullSubdiff 1 (@hardValue M N) z) :
    HardFormulaReply z g := by
  have hgsharp := fullSubdiff_one_subset_threeQuarter hA z hg
  rw [mem_fullSubdiff_iff_qSubgradient] at hgsharp
  norm_num at hgsharp
  exact qSubgradient_threeEighths_hardFormulaReply hA hR hgsharp

/-- Proposition-valued wrapper around the explicit positive-activation
formula constructor. -/
theorem fullSubdiff_one_positive_has_hardFormulaReply {M N : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hR : 0 < activationNorm z)
    (hg : g ∈ fullSubdiff 1 (@hardValue M N) z) :
    Nonempty (HardFormulaReply z g) :=
  ⟨fullSubdiff_one_positive_hardFormulaReply hA hR hg⟩

/-! ## Direct zero-activation locality -/

/-- Moving a coordinate away from zero cannot decrease the progress carrier,
because the changed scalar gate is nonnegative and `q(0)=0`. -/
theorem psi_le_shiftCoord_of_coord_eq_zero {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) (i : Fin N) (s : ℝ) (hui : u i = 0) :
    psi u ≤ psi (shiftCoord u i s) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold psi
  apply (div_le_div_iff_of_pos_right hNreal).2
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    rw [shiftCoord_same, hui]
    simp only [zero_add, mul_zero, zero_div, q_zero]
    exact q_nonneg _
  · rw [shiftCoord_ne u hji s]

/-- A negative coordinate shift can raise at most its own affine facet. -/
theorem phi_shiftCoord_le_of_nonpos {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) (i : Fin N) {s : ℝ} (hs : s ≤ 0) :
    phi (shiftCoord u i s) ≤ phi u - (N : ℝ) / 8 * s := by
  have hinc : 0 ≤ -((N : ℝ) / 8 * s) := by
    have hc : 0 ≤ (N : ℝ) / 8 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hs]
  change (Finset.univ : Finset (FacetIndex N)).sup'
      Finset.univ_nonempty (facetValue (shiftCoord u i s)) ≤
    phi u - (N : ℝ) / 8 * s
  apply Finset.sup'_le Finset.univ_nonempty
  intro r _
  cases r with
  | none =>
      have h0 := phi_nonneg u
      simp only [facetValue_none]
      linarith
  | some j =>
      by_cases hji : j = i
      · subst j
        rw [facetValue_shiftCoord_same]
        exact sub_le_sub_right (facetValue_le_phi u (some i)) _
      · rw [facetValue_shiftCoord_ne u hji s]
        have hbase := facetValue_le_phi u (some j)
        linarith

/-- If the changed fan contribution is nonpositive and progress does not
decrease, the canonical branch at the changed point certifies that the whole
hard value does not increase. -/
theorem hardValue_blockLine_le_of_canonical_fan_nonpos {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ)
    (hfan : canonicalOuterWeight (sigmaScore (blockLine z m v t)) m *
        (phi (blockLine z m v t m) - phi (z m)) ≤ 0)
    (hpsi : psi (z m) ≤ psi (blockLine z m v t m)) :
    hardValue (blockLine z m v t) ≤ hardValue z := by
  let y := blockLine z m v t
  let w := canonicalOuterWeight (sigmaScore y)
  have hw : FeasibleOuterWeight w := canonicalOuterWeight_feasible _
  have hy : activationBranch w y = hardValue y := by
    simpa [w] using activationBranch_canonical_eq_hardValue y
  have hzle : activationBranch w z ≤ hardValue z :=
    activationBranch_le_hardValue hN hw z
  have hdiff := activationBranch_blockLine_sub_eq hM w z m v t
  change activationBranch w y - activationBranch w z =
      (2 / (N : ℝ)) *
        (w m * (phi (y m) - phi (z m)) -
          netProgressWeight w m * (psi (y m) - psi (z m))) at hdiff
  have hfan' : w m * (phi (y m) - phi (z m)) ≤ 0 := by
    simpa [w, y] using hfan
  have ha0 := netProgressWeight_nonneg hw m
  have hprog : 0 ≤ netProgressWeight w m * (psi (y m) - psi (z m)) :=
    mul_nonneg ha0 (sub_nonneg.mpr (by simpa [y] using hpsi))
  have hscale : 0 ≤ 2 / (N : ℝ) := by positivity
  have hbranch : activationBranch w y ≤ activationBranch w z := by
    apply sub_nonpos.mp
    rw [hdiff]
    apply mul_nonpos_of_nonneg_of_nonpos hscale
    linarith
  rw [← hy]
  exact hbranch.trans hzle

theorem hardValue_blockLine_le_of_phi_le {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ)
    (hphi : phi (blockLine z m v t m) ≤ phi (z m))
    (hpsi : psi (z m) ≤ psi (blockLine z m v t m)) :
    hardValue (blockLine z m v t) ≤ hardValue z := by
  apply hardValue_blockLine_le_of_canonical_fan_nonpos hM hN z m v t
  · exact mul_nonpos_of_nonneg_of_nonpos
      (canonicalOuterWeight_nonneg _ m) (sub_nonpos.mpr hphi)
  · exact hpsi

/-- An inactive tilted facet admits a nontrivial negative segment on which
the finite maximum is exactly constant. -/
theorem exists_negative_phi_shift_segment_eq_of_inactive {N : Nat}
    (hN : 0 < N) (u : Fin N → ℝ) (i : Fin N)
    (hi : ¬ ActiveFacet u (some i)) :
    ∃ r : ℝ, r < 0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      phi (shiftCoord u i (θ * r)) = phi u := by
  let δ := phi u - facetValue u (some i)
  have hδ : 0 < δ := by
    have hle := facetValue_le_phi u (some i)
    have hne : facetValue u (some i) ≠ phi u := by
      intro heq
      exact hi heq
    dsimp [δ]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  let r := -8 * δ / (N : ℝ)
  have hr : r < 0 := by
    dsimp [r]
    exact div_neg_of_neg_of_pos (by nlinarith) (by exact_mod_cast hN)
  refine ⟨r, hr, ?_⟩
  intro θ hθ0 hθ1
  apply le_antisymm
  · change (Finset.univ : Finset (FacetIndex N)).sup'
        Finset.univ_nonempty (facetValue (shiftCoord u i (θ * r))) ≤ phi u
    apply Finset.sup'_le Finset.univ_nonempty
    intro s _
    cases s with
    | none => exact phi_nonneg u
    | some j =>
        by_cases hji : j = i
        · subst j
          rw [facetValue_shiftCoord_same]
          have heq : (N : ℝ) / 8 * (θ * r) = -θ * δ := by
            dsimp [r]
            field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]
          rw [heq]
          have hδeq : δ = phi u - facetValue u (some i) := rfl
          nlinarith [facetValue_le_phi u (some i)]
        · rw [facetValue_shiftCoord_ne u hji (θ * r)]
          exact facetValue_le_phi u (some j)
  · obtain ⟨s, hs⟩ := exists_activeFacet u
    have hsi : s ≠ some i := by
      intro h
      subst s
      exact hi hs
    calc
      phi u = facetValue u s := hs.symm
      _ = facetValue (shiftCoord u i (θ * r)) s := by
        cases s with
        | none => rfl
        | some j =>
            have hji : j ≠ i := by
              intro h
              subst j
              exact hsi rfl
            exact (facetValue_shiftCoord_ne u hji (θ * r)).symm
      _ ≤ phi (shiftCoord u i (θ * r)) :=
        facetValue_le_phi _ s

@[simp] theorem blockLine_shiftCoord_same {M N : Nat}
    (z : BlockVec M N) (m : Fin M) (j : Fin N) (r θ : ℝ) :
    blockLine z m (shiftCoord (z m) j r) θ m =
      shiftCoord (z m) j (θ * r) := by
  ext i
  by_cases h : i = j
  · simp [blockLine_same, shiftCoord, h]
    ring
  · simp [blockLine_same, shiftCoord, h]
    ring

theorem canonicalOuterWeight_coord_eq_zero_of_nonpos {M : Nat}
    (s : Fin M → ℝ) (m : Fin M) (hm : s m ≤ 0) :
    canonicalOuterWeight s m = 0 := by
  simp [canonicalOuterWeight, max_eq_right hm]

theorem hardValue_blockLine_le_of_canonical_weight_zero {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) (z : BlockVec M N) (m : Fin M)
    (v : Fin N → ℝ) (t : ℝ)
    (hweight : canonicalOuterWeight (sigmaScore (blockLine z m v t)) m = 0)
    (hpsi : psi (z m) ≤ psi (blockLine z m v t m)) :
    hardValue (blockLine z m v t) ≤ hardValue z := by
  apply hardValue_blockLine_le_of_canonical_fan_nonpos hM hN z m v t
  · rw [hweight, zero_mul]
  · exact hpsi

/-- A block whose zero-th coordinate is still beyond the next diagonal level
is identically zero and has a strictly negative phase score. -/
theorem unreached_zero_index_block_zero_sigma_neg {M N t : Nat}
    (hA : Admissible M N) {z : BlockVec M N}
    (hz : Reachable (relayDelay N) t z) (m : Fin M)
    (hlevel : t + 1 ≤ level (relayDelay N) m.1 0) :
    z m = 0 ∧ sigmaScore z m < 0 := by
  have hm0 : m.1 ≠ 0 := by
    intro hm
    simp [level, hm] at hlevel
  let mp : Fin M := ⟨m.1 - 1, by omega⟩
  have hbase : t + 1 ≤ m.1 * relayDelay N := by
    simpa [level] using hlevel
  have hmdecomp : m.1 = (m.1 - 1) + 1 := by omega
  have hblock : z m = 0 := by
    funext i
    apply hz m i
    unfold level at hlevel ⊢
    omega
  have hprevPrefix : PrefixSupported (relayDelay N) (z mp) := by
    intro i hi
    apply hz mp i
    have hbase' := hbase
    rw [hmdecomp, Nat.add_mul] at hbase'
    change t ≤ (m.1 - 1) * relayDelay N + i.1
    omega
  have hpsi : psi (z mp) ≤ (relayDelay N : ℝ) / (N : ℝ) :=
    psi_le_prefix hA.N_pos
      (Nat.le_of_lt (relayDelay_lt hA.N_pos)) hprevPrefix
  have hratio := relayDelay_ratio_le hA.N_pos
  have hprev : previousProgress z m = psi (z mp) := by
    simp only [previousProgress, dif_neg hm0]
    congr 1
  have hphi : phi (z m) = intercept N (firstCoord hA.N_pos) := by
    rw [hblock]
    exact phi_zero_eq_intercept_first hA.N_pos
  have hc := intercept_first_add_three_sixteenths_lt_five_fourths hA.N_pos
  refine ⟨hblock, ?_⟩
  unfold sigmaScore
  rw [hphi, hprev]
  linarith

/-- At an unreached block's zero-th coordinate there is a negative segment
on which the hard value cannot increase. -/
theorem exists_negative_zero_index_hardValue_blockLine_le {M N t : Nat}
    (hA : Admissible M N) {z : BlockVec M N}
    (hz : Reachable (relayDelay N) t z) (m : Fin M) (j : Fin N)
    (hj : j.1 = 0)
    (hlevel : t + 1 ≤ level (relayDelay N) m.1 j.1) :
    ∃ r : ℝ, r < 0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j r) θ) ≤ hardValue z := by
  have hlevel0 : t + 1 ≤ level (relayDelay N) m.1 0 := by
    simpa [hj] using hlevel
  obtain ⟨hblock, hsneg⟩ :=
    unreached_zero_index_block_zero_sigma_neg hA hz m hlevel0
  have hm0 : m.1 ≠ 0 := by
    intro hm
    simp [level, hm] at hlevel0
  let δ := -sigmaScore z m
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let r := -4 * δ / (N : ℝ)
  have hr : r < 0 := by
    dsimp [r]
    exact div_neg_of_neg_of_pos (by nlinarith) (by exact_mod_cast hA.N_pos)
  refine ⟨r, hr, ?_⟩
  intro θ hθ0 hθ1
  let y := blockLine z m (shiftCoord (z m) j r) θ
  have hzj : z m j = 0 := by rw [hblock]; rfl
  have hpsi : psi (z m) ≤ psi (y m) := by
    dsimp [y]
    rw [blockLine_shiftCoord_same]
    exact psi_le_shiftCoord_of_coord_eq_zero hA.N_pos (z m) j (θ * r) hzj
  have hs : θ * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ0 hr.le
  have hphi : phi (y m) ≤ phi (z m) - (N : ℝ) / 8 * (θ * r) := by
    dsimp [y]
    rw [blockLine_shiftCoord_same]
    exact phi_shiftCoord_le_of_nonpos hA.N_pos (z m) j hs
  let mp : Fin M := ⟨m.1 - 1, by omega⟩
  have hmp : mp ≠ m := by
    intro heq
    have := congrArg Fin.val heq
    dsimp [mp] at this
    omega
  have hprev : previousProgress y m = previousProgress z m := by
    unfold previousProgress
    simp only [dif_neg hm0]
    congr 1
    exact blockLine_other z hmp (shiftCoord (z m) j r) θ
  have heq : (N : ℝ) / 8 * (θ * r) = -θ * δ / 2 := by
    dsimp [r]
    field_simp [show (N : ℝ) ≠ 0 by
      exact_mod_cast (Nat.ne_of_gt hA.N_pos)]
    ring
  have hscore : sigmaScore y m < 0 := by
    have hδeq : δ = -sigmaScore z m := rfl
    have hscoreDiff : sigmaScore y m ≤
        sigmaScore z m - (N : ℝ) / 8 * (θ * r) := by
      unfold sigmaScore
      rw [hprev]
      linarith
    rw [heq] at hscoreDiff
    nlinarith
  have hweight : canonicalOuterWeight (sigmaScore y) m = 0 :=
    canonicalOuterWeight_coord_eq_zero_of_nonpos _ m hscore.le
  dsimp [y] at hweight hpsi ⊢
  exact hardValue_blockLine_le_of_canonical_weight_zero
    hA.M_pos hA.N_pos z m (shiftCoord (z m) j r) θ hweight hpsi

theorem vecSq_shiftCoord_sub {N : Nat} (u : Fin N → ℝ)
    (j : Fin N) (r : ℝ) :
    vecSq (shiftCoord u j r - u) = r ^ 2 := by
  classical
  unfold vecSq shiftCoord
  simp

/-- A quadratic support vector tested along a nonincreasing coordinate
segment has nonpositive pairing with that segment direction. -/
theorem qSubgradient_hardValue_coord_mul_nonpos_of_segment {M N : Nat}
    {z g : BlockVec M N}
    (hg : QSubgradient (3 / 8 : ℝ) (@hardValue M N) z g)
    (m : Fin M) (j : Fin N) (r : ℝ)
    (hdec : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j r) θ) ≤ hardValue z) :
    g m j * r ≤ 0 := by
  apply linear_le_of_segment_quadratic
    (A := g m j * r) (B := 0) (C := (3 / 8 : ℝ) * r ^ 2)
  intro θ hθ hθ1
  let y := blockLine z m (shiftCoord (z m) j r) θ
  have hq := hg y
  have hdot : blockDot g (y - z) = θ * (g m j * r) := by
    dsimp [y]
    rw [blockDot_blockLine_sub, vecDot_shiftCoord_sub]
  have hsq : blockSq (y - z) = θ ^ 2 * r ^ 2 := by
    dsimp [y]
    rw [blockSq_blockLine_sub, vecSq_shiftCoord_sub]
  rw [hdot, hsq] at hq
  have hy := hdec θ hθ hθ1
  change hardValue y ≤ hardValue z at hy
  nlinarith

/-- Direct semantic proof of C2.  It uses only the global quadratic support
inequality: every coordinate beyond the next diagonal level admits both a
positive and a negative nonincreasing hard-value segment, so its support
coefficient must vanish. -/
theorem hardValue_fullSubdiff_locality {M N : Nat}
    (hA : Admissible M N) :
    HasDiagonalLocality (relayDelay N)
      (fullSubdiff 1 (hardValue : BlockVec M N → ℝ)) := by
  intro t z hz g hg m j hlevel
  have hzj : z m j = 0 := hz m j (by omega)
  have hgsharp := fullSubdiff_one_subset_threeQuarter hA z hg
  rw [mem_fullSubdiff_iff_qSubgradient] at hgsharp
  norm_num at hgsharp
  have hposSegment : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j 1) θ) ≤ hardValue z := by
    intro θ hθ hθ1
    have hθ0 : 0 ≤ θ := hθ.le
    apply hardValue_blockLine_le_of_phi_le
      hA.M_pos hA.N_pos z m (shiftCoord (z m) j 1) θ
    · rw [blockLine_shiftCoord_same]
      exact phi_shiftCoord_le hA.N_pos (z m) j (by positivity)
    · rw [blockLine_shiftCoord_same]
      exact psi_le_shiftCoord_of_coord_eq_zero
        hA.N_pos (z m) j (θ * 1) hzj
  have hg_nonpos : g m j ≤ 0 := by
    have h := qSubgradient_hardValue_coord_mul_nonpos_of_segment
      hgsharp m j 1 hposSegment
    simpa using h
  have hnegSegment : ∃ r : ℝ, r < 0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      hardValue (blockLine z m (shiftCoord (z m) j r) θ) ≤ hardValue z := by
    by_cases hj0 : j.1 = 0
    · exact exists_negative_zero_index_hardValue_blockLine_le
        hA hz m j hj0 hlevel
    · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj0
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
        intro hjactive
        have hidx := activeFacet_index_le_first_hidden
          hA.N_pos hkN hzprefix hjactive
        dsimp [k] at hidx
        omega
      obtain ⟨r, hr, hphi⟩ :=
        exists_negative_phi_shift_segment_eq_of_inactive
          hA.N_pos (z m) j hinactive
      refine ⟨r, hr, ?_⟩
      intro θ hθ0 hθ1
      apply hardValue_blockLine_le_of_phi_le
        hA.M_pos hA.N_pos z m (shiftCoord (z m) j r) θ
      · rw [blockLine_shiftCoord_same, hphi θ hθ0 hθ1]
      · rw [blockLine_shiftCoord_same]
        exact psi_le_shiftCoord_of_coord_eq_zero
          hA.N_pos (z m) j (θ * r) hzj
  obtain ⟨r, hr, hnegSegment⟩ := hnegSegment
  have hmul := qSubgradient_hardValue_coord_mul_nonpos_of_segment
    hgsharp m j r (fun θ hθ hθ1 ↦ hnegSegment θ hθ.le hθ1)
  have hg_nonneg : 0 ≤ g m j := by nlinarith
  exact le_antisymm hg_nonpos hg_nonneg

end

end WeaklyConvexLowerBound

