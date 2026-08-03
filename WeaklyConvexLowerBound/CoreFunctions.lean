import WeaklyConvexLowerBound.Basic
import WeaklyConvexLowerBound.Foundation.Smoothstep

/-!
# Core scalar and tilted-block functions

This file checks the elementary identities used by the hard instance in
the weakly convex lower-bound manuscript.  In particular, it gives a completely explicit
finite model of the full subdifferential of the tilted max-affine block: a
vector in that model is a convex combination of the slopes of active facets.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-! ## The cubic progress step -/

/-- The clipped cubic smoothstep from the manuscript. -/
def q (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t < 1 then 3 * t ^ 2 - 2 * t ^ 3 else 1

/-- The piecewise derivative displayed in the proof of progress regularity. -/
def qPrime (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t < 1 then 6 * t * (1 - t) else 0

@[simp] theorem q_of_nonpos {t : ℝ} (ht : t ≤ 0) : q t = 0 := by
  simp [q, ht]

theorem q_of_pos_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    q t = 3 * t ^ 2 - 2 * t ^ 3 := by
  simp [q, not_le.mpr h0, h1]

@[simp] theorem q_of_one_le {t : ℝ} (ht : 1 ≤ t) : q t = 1 := by
  have h0 : ¬ t ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ht)
  simp [q, h0, not_lt.mpr ht]

@[simp] theorem qPrime_of_nonpos {t : ℝ} (ht : t ≤ 0) : qPrime t = 0 := by
  simp [qPrime, ht]

theorem qPrime_of_pos_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    qPrime t = 6 * t * (1 - t) := by
  simp [qPrime, not_le.mpr h0, h1]

@[simp] theorem qPrime_of_one_le {t : ℝ} (ht : 1 ≤ t) : qPrime t = 0 := by
  have h0 : ¬ t ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ht)
  simp [qPrime, h0, not_lt.mpr ht]

@[simp] theorem q_zero : q 0 = 0 := by
  exact q_of_nonpos le_rfl

@[simp] theorem qPrime_zero : qPrime 0 = 0 := by
  exact qPrime_of_nonpos le_rfl

@[simp] theorem q_one : q 1 = 1 := by
  exact q_of_one_le le_rfl

@[simp] theorem qPrime_one : qPrime 1 = 0 := by
  exact qPrime_of_one_le le_rfl

theorem q_three_quarters : q ((3 : ℝ) / 4) = 27 / 32 := by
  rw [q_of_pos_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem qPrime_nonneg (t : ℝ) : 0 ≤ qPrime t := by
  by_cases h0 : t ≤ 0
  · simp [qPrime, h0]
  · have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [qPrime_of_pos_of_lt_one ht h1]
      positivity
    · rw [qPrime_of_one_le (le_of_not_gt h1)]

theorem qPrime_le_three_halves (t : ℝ) : qPrime t ≤ (3 : ℝ) / 2 := by
  by_cases h0 : t ≤ 0
  · rw [qPrime_of_nonpos h0]
    norm_num
  · have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [qPrime_of_pos_of_lt_one ht h1]
      nlinarith [sq_nonneg (2 * t - 1)]
    · rw [qPrime_of_one_le (le_of_not_gt h1)]
      norm_num

theorem q_nonneg (t : ℝ) : 0 ≤ q t := by
  by_cases h0 : t ≤ 0
  · simp [q, h0]
  · have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [q_of_pos_of_lt_one ht h1]
      have : 0 < 3 - 2 * t := by linarith
      nlinarith [sq_nonneg t]
    · rw [q_of_one_le (le_of_not_gt h1)]
      norm_num

theorem q_le_one (t : ℝ) : q t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · simp [q, h0]
  · have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [q_of_pos_of_lt_one ht h1]
      nlinarith [sq_nonneg (1 - t), mul_nonneg (sq_nonneg (1 - t)) (by linarith : 0 ≤ 1 + 2 * t)]
    · rw [q_of_one_le (le_of_not_gt h1)]

theorem q_mem_unitInterval (t : ℝ) : q t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨q_nonneg t, q_le_one t⟩

/-- Algebraic monotonicity inside the polynomial transition interval. -/
theorem q_transition_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    3 * a ^ 2 - 2 * a ^ 3 ≤ 3 * b ^ 2 - 2 * b ^ 3 := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsum : 0 ≤ 3 * (a + b) - 2 * (a ^ 2 + a * b + b ^ 2) := by
    have h₁ : 0 ≤ a * (1 - a) :=
      mul_nonneg ha0 (sub_nonneg.mpr (hab.trans hb1))
    have h₂ : 0 ≤ b * (1 - b) := mul_nonneg (ha0.trans hab) (sub_nonneg.mpr hb1)
    have h₃ : 0 ≤ (b - a) * (1 - b) := mul_nonneg hba (sub_nonneg.mpr hb1)
    nlinarith
  nlinarith

theorem q_monotone : Monotone q := by
  intro a b hab
  by_cases ha : a ≤ 0
  · rw [q_of_nonpos ha]
    exact q_nonneg b
  · have ha0 : 0 < a := lt_of_not_ge ha
    by_cases hb : 1 ≤ b
    · rw [q_of_one_le hb]
      exact q_le_one a
    · have hb1 : b < 1 := lt_of_not_ge hb
      have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
      rw [q_of_pos_of_lt_one ha0 (lt_of_le_of_lt hab hb1),
        q_of_pos_of_lt_one hb0 hb1]
      exact q_transition_mono ha0.le hab hb1.le

theorem q_le_three_mul_posPart_sq (t : ℝ) :
    q t ≤ 3 * (max t 0) ^ 2 := by
  by_cases h0 : t ≤ 0
  · simp [q_of_nonpos h0, max_eq_right h0]
  · have ht : 0 < t := lt_of_not_ge h0
    rw [max_eq_left ht.le]
    by_cases h1 : t < 1
    · rw [q_of_pos_of_lt_one ht h1]
      have : 0 ≤ t ^ 3 := by positivity
      nlinarith
    · rw [q_of_one_le (le_of_not_gt h1)]
      nlinarith [sq_nonneg t]

/-! ### Analytic splice certificates

The construction's cubic gate is extensionally equal to the support module's
canonical clipped smoothstep.  The only syntactic differences are `< 1`
versus `≤ 1` at a junction where both formulas equal one, and the factored
derivative formula.
-/

theorem q_eq_foundationSigma : q = WeaklyConvexLowerBound.Foundation.sigma := by
  funext t
  by_cases h0 : t ≤ 0
  · simp [q, WeaklyConvexLowerBound.Foundation.sigma, h0]
  · by_cases h1 : t < 1
    · have h1le : t ≤ 1 := h1.le
      simp [q, WeaklyConvexLowerBound.Foundation.sigma, h0, h1, h1le]
    · have hge : 1 ≤ t := le_of_not_gt h1
      rcases hge.eq_or_lt with heq | hgt
      · subst t
        norm_num [q, WeaklyConvexLowerBound.Foundation.sigma]
      · have hnle : ¬ t ≤ 1 := not_le.mpr hgt
        simp [q, WeaklyConvexLowerBound.Foundation.sigma, h0, h1, hnle]

theorem qPrime_eq_foundationSigmaDeriv :
    qPrime = WeaklyConvexLowerBound.Foundation.sigmaDeriv := by
  funext t
  by_cases h0 : t ≤ 0
  · simp [qPrime, WeaklyConvexLowerBound.Foundation.sigmaDeriv, h0]
  · by_cases h1 : t < 1
    · have h1le : t ≤ 1 := h1.le
      simp only [qPrime, WeaklyConvexLowerBound.Foundation.sigmaDeriv, if_neg h0,
        if_pos h1, if_pos h1le]
      ring
    · have hge : 1 ≤ t := le_of_not_gt h1
      rcases hge.eq_or_lt with heq | hgt
      · subst t
        norm_num [qPrime, WeaklyConvexLowerBound.Foundation.sigmaDeriv]
      · have hnle : ¬ t ≤ 1 := not_le.mpr hgt
        simp [qPrime, WeaklyConvexLowerBound.Foundation.sigmaDeriv, h0, h1, hnle]

/-- `qPrime` is the actual derivative, including at both splice points. -/
theorem hasDerivAt_q (t : ℝ) : HasDerivAt q (qPrime t) t := by
  rw [q_eq_foundationSigma, qPrime_eq_foundationSigmaDeriv]
  exact WeaklyConvexLowerBound.Foundation.hasDerivAt_sigma t

theorem deriv_q (t : ℝ) : deriv q t = qPrime t :=
  (hasDerivAt_q t).deriv

theorem differentiable_q : Differentiable ℝ q :=
  fun t => (hasDerivAt_q t).differentiableAt

/-- The literal `q'(0)=0` certificate used in the relay argument. -/
theorem deriv_q_zero : deriv q 0 = 0 := by
  rw [deriv_q, qPrime_zero]

/-- The global scalar estimate behind `Lip(q') ≤ 6`. -/
theorem qPrime_abs_sub_le (a b : ℝ) :
    |qPrime a - qPrime b| ≤ 6 * |a - b| := by
  rw [qPrime_eq_foundationSigmaDeriv]
  exact WeaklyConvexLowerBound.Foundation.sigmaDeriv_abs_sub_le a b

theorem qPrime_lipschitzWith : LipschitzWith (6 : NNReal) qPrime := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa [Real.dist_eq] using qPrime_abs_sub_le a b

theorem qPrime_continuous : Continuous qPrime :=
  qPrime_lipschitzWith.continuous

/-! ## The tilted max-affine block -/

/-- Zero-based version of the manuscript's intercept
`c_j = 1 + (N-j)/(16N)`, where the paper numbers `j` from one. -/
def intercept (N : Nat) (j : Fin N) : ℝ :=
  1 + ((N : ℝ) - (j.1 : ℝ) - 1) / (16 * (N : ℝ))

theorem intercept_ge_one {N : Nat} (hN : 0 < N) (j : Fin N) :
    1 ≤ intercept N j := by
  have hj : (j.1 : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.2
  have hden : 0 < (16 : ℝ) * N := by positivity
  unfold intercept
  have hnum : 0 ≤ (N : ℝ) - (j.1 : ℝ) - 1 := by linarith
  exact le_add_of_nonneg_right (div_nonneg hnum hden.le)

/-- The intercepts are strictly decreasing in the facet number. -/
theorem intercept_strictAnti {N : Nat} (hN : 0 < N) {i j : Fin N}
    (hij : i.1 < j.1) : intercept N j < intercept N i := by
  have hijR : (i.1 : ℝ) < (j.1 : ℝ) := by exact_mod_cast hij
  have hden : 0 < (16 : ℝ) * N := by positivity
  unfold intercept
  rw [add_lt_add_iff_left]
  exact (div_lt_div_iff_of_pos_right hden).2 (by linarith)

theorem intercept_last (N : Nat) : intercept (N + 1) (Fin.last N) = 1 := by
  unfold intercept
  change 1 + (((N + 1 : Nat) : ℝ) - (N : ℝ) - 1) /
      (16 * ((N + 1 : Nat) : ℝ)) = 1
  have hnum : (((N + 1 : Nat) : ℝ) - (N : ℝ) - 1) = 0 := by
    push_cast
    ring
  rw [hnum, zero_div, add_zero]

/-- The extra index `none` denotes the constant zero branch of `phi`. -/
abbrev FacetIndex (N : Nat) := Option (Fin N)

/-- Value of a single branch of the max-affine block. -/
def facetValue {N : Nat} (u : Fin N → ℝ) : FacetIndex N → ℝ
  | none => 0
  | some j => intercept N j - (N : ℝ) / 8 * u j

/-- Slope of a single branch of the max-affine block. -/
def facetSlope {N : Nat} : FacetIndex N → Fin N → ℝ
  | none, _ => 0
  | some j, i => if i = j then -(N : ℝ) / 8 else 0

@[simp] theorem facetValue_none {N : Nat} (u : Fin N → ℝ) :
    facetValue u none = 0 := rfl

@[simp] theorem facetValue_some {N : Nat} (u : Fin N → ℝ) (j : Fin N) :
    facetValue u (some j) = intercept N j - (N : ℝ) / 8 * u j := rfl

@[simp] theorem facetSlope_none {N : Nat} (i : Fin N) :
    facetSlope (none : FacetIndex N) i = 0 := rfl

@[simp] theorem facetSlope_some_same {N : Nat} (j : Fin N) :
    facetSlope (some j) j = -(N : ℝ) / 8 := by
  simp [facetSlope]

theorem facetSlope_some_ne {N : Nat} {i j : Fin N} (hij : i ≠ j) :
    facetSlope (some j) i = 0 := by
  simp [facetSlope, hij]

/-- The paper's tilted block, including its constant zero branch. -/
def phi {N : Nat} (u : Fin N → ℝ) : ℝ :=
  (Finset.univ : Finset (FacetIndex N)).sup' Finset.univ_nonempty (facetValue u)

/-- A facet is active precisely when its value realizes the finite maximum. -/
def ActiveFacet {N : Nat} (u : Fin N → ℝ) (s : FacetIndex N) : Prop :=
  facetValue u s = phi u

theorem facetValue_le_phi {N : Nat} (u : Fin N → ℝ) (s : FacetIndex N) :
    facetValue u s ≤ phi u := by
  unfold phi
  exact Finset.le_sup' (facetValue u) (Finset.mem_univ s)

theorem phi_nonneg {N : Nat} (u : Fin N → ℝ) : 0 ≤ phi u := by
  simpa using facetValue_le_phi u (none : FacetIndex N)

theorem exists_activeFacet {N : Nat} (u : Fin N → ℝ) :
    ∃ s : FacetIndex N, ActiveFacet u s := by
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (facetValue u)
  refine ⟨s, ?_⟩
  change facetValue u s = phi u
  exact hs.symm

theorem activeFacet_iff_maximal {N : Nat} (u : Fin N → ℝ)
    (s : FacetIndex N) :
    ActiveFacet u s ↔ ∀ r : FacetIndex N, facetValue u r ≤ facetValue u s := by
  constructor
  · intro hs r
    change facetValue u s = phi u at hs
    rw [hs]
    exact facetValue_le_phi u r
  · intro hs
    change facetValue u s = phi u
    apply le_antisymm
    · exact facetValue_le_phi u s
    · unfold phi
      exact Finset.sup'_le Finset.univ_nonempty (facetValue u)
        (fun r _ => hs r)

/-- If only the first `k` coordinates can be nonzero, no active nonzero
branch can have index beyond the first hidden coordinate `k`. -/
theorem activeFacet_index_le_first_hidden {N k : Nat} (hN : 0 < N)
    (hk : k < N) {u : Fin N → ℝ} (hu : PrefixSupported k u)
    {j : Fin N} (hj : ActiveFacet u (some j)) : j.1 ≤ k := by
  change facetValue u (some j) = phi u at hj
  by_contra hjk
  have hkj : k < j.1 := Nat.lt_of_not_ge hjk
  let i : Fin N := ⟨k, hk⟩
  have hui : u i = 0 := hu i le_rfl
  have huj : u j = 0 := hu j hkj.le
  have hc : intercept N j < intercept N i :=
    intercept_strictAnti hN hkj
  have hv : facetValue u (some j) < facetValue u (some i) := by
    simp only [facetValue_some, hui, huj, mul_zero, sub_zero]
    exact hc
  have hle : facetValue u (some i) ≤ facetValue u (some j) := by
    rw [hj]
    exact facetValue_le_phi u (some i)
  exact (not_lt_of_ge hle) hv

theorem activeFacet_slope_hidden_eq_zero {N k : Nat} (hN : 0 < N)
    (hk : k < N) {u : Fin N → ℝ} (hu : PrefixSupported k u)
    {s : FacetIndex N} (hs : ActiveFacet u s) {i : Fin N}
    (hi : k + 1 ≤ i.1) : facetSlope s i = 0 := by
  cases s with
  | none => rfl
  | some j =>
      have hj : j.1 ≤ k :=
        activeFacet_index_le_first_hidden hN hk hu hs
      have hij : i ≠ j := by
        intro hij
        subst i
        omega
      exact facetSlope_some_ne hij

/-! ### A finite, exact model of the full block subdifferential -/

/-- `g ∈ ∂phi(u)` in the finite max-affine model: `g` is a convex
combination of slopes of active branches.  Keeping the weights explicit is
useful because the oracle in the manuscript returns the *entire* set. -/
def PhiSubgradient {N : Nat} (u g : Fin N → ℝ) : Prop :=
  ∃ weights : FacetIndex N → ℝ,
    (∀ s, 0 ≤ weights s) ∧
    (∑ s, weights s) = 1 ∧
    (∀ s, weights s ≠ 0 → ActiveFacet u s) ∧
    (∀ i, g i = ∑ s, weights s * facetSlope s i)

/-- The missing tilted-block locality lemma from the TeX proof, stated for
the full set of convex combinations rather than for a selected slope. -/
theorem phiSubgradient_locality {N k : Nat} (hN : 0 < N) (hk : k < N)
    {u g : Fin N → ℝ} (hu : PrefixSupported k u)
    (hg : PhiSubgradient u g) : PrefixSupported (k + 1) g := by
  obtain ⟨weights, _hweights_nonneg, _hweights_sum, hweights_active, hgcoord⟩ := hg
  intro i hi
  rw [hgcoord i]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hweight : weights s = 0
  · simp [hweight]
  · have hs : ActiveFacet u s := hweights_active s hweight
    rw [activeFacet_slope_hidden_eq_zero (N := N) (k := k) hN hk hu hs hi]
    simp

theorem activeFacet_slope_is_PhiSubgradient {N : Nat} (u : Fin N → ℝ)
    {s : FacetIndex N} (hs : ActiveFacet u s) :
    PhiSubgradient u (facetSlope s) := by
  let weights : FacetIndex N → ℝ := fun r => if r = s then 1 else 0
  refine ⟨weights, ?_, ?_, ?_, ?_⟩
  · intro r
    dsimp [weights]
    split <;> norm_num
  · classical
    simp [weights]
  · intro r hr
    have hrs : r = s := by
      by_contra hrs
      exact hr (by simp [weights, hrs])
    simpa [hrs] using hs
  · intro i
    classical
    simp [weights]

end

end WeaklyConvexLowerBound


