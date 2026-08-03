import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.HardInstance
import WeaklyConvexLowerBound.Variational
import Mathlib.Analysis.Convex.Deriv

/-!
# Concrete regularity of the normalized hard instance

This file proves the analytic ingredients of condition (C1) for the literal
`hardValue` used in the manuscript.  All estimates use `blockSq`, i.e. the
sum-of-squares Euclidean geometry of the paper, and not the sup norm carried
by Lean's finite Pi type.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-! ## The scalar curvature certificate -/

/-- Adding the sharp quadratic correction to `-q`. -/
def qConvexified (t : ℝ) : ℝ := -q t + 3 * t ^ 2

theorem hasDerivAt_qConvexified (t : ℝ) :
    HasDerivAt qConvexified (-qPrime t + 6 * t) t := by
  change HasDerivAt (fun x : ℝ ↦ -q x + 3 * x ^ 2)
    (-qPrime t + 6 * t) t
  have hneg : HasDerivAt (fun x : ℝ ↦ -q x) (-qPrime t) t :=
    (hasDerivAt_q t).neg
  have hquad : HasDerivAt (fun x : ℝ ↦ 3 * x ^ 2) (6 * t) t := by
    have h := HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_pow 2 t)
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    exact h.congr_deriv (by ring)
  exact hneg.add hquad

theorem deriv_qConvexified (t : ℝ) :
    deriv qConvexified t = -qPrime t + 6 * t :=
  (hasDerivAt_qConvexified t).deriv

theorem differentiable_qConvexified : Differentiable ℝ qConvexified :=
  fun t ↦ (hasDerivAt_qConvexified t).differentiableAt

/-- The derivative of the corrected scalar is monotone.  This is exactly the
one-dimensional form of the global lower Hessian bound `q'' ≥ -6`. -/
theorem qConvexified_deriv_monotone :
    Monotone (fun t : ℝ ↦ -qPrime t + 6 * t) := by
  intro a b hab
  have hq := qPrime_abs_sub_le b a
  have hba : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
  have hupper : qPrime b - qPrime a ≤ 6 * (b - a) := by
    calc
      qPrime b - qPrime a ≤ |qPrime b - qPrime a| := le_abs_self _
      _ ≤ 6 * |b - a| := hq
      _ = 6 * (b - a) := by rw [hba]
  linarith

theorem qConvexified_convexOn : ConvexOn ℝ Set.univ qConvexified := by
  apply Monotone.convexOn_univ_of_deriv differentiable_qConvexified
  rw [show deriv qConvexified = (fun t : ℝ ↦ -qPrime t + 6 * t) by
    funext t
    exact deriv_qConvexified t]
  exact qConvexified_deriv_monotone

/-- The scalar progress step is globally `3/2`-Lipschitz. -/
theorem q_lipschitzWith : LipschitzWith (3 / 2 : NNReal) q := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_q
  intro t
  rw [deriv_q]
  apply NNReal.coe_le_coe.1
  simp only [coe_nnnorm, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.norm_eq_abs, abs_of_nonneg (qPrime_nonneg t)]
  exact qPrime_le_three_halves t

theorem q_abs_sub_le (a b : ℝ) :
    |q a - q b| ≤ (3 / 2 : ℝ) * |a - b| := by
  simpa [Real.dist_eq] using q_lipschitzWith.dist_le_mul a b

/-! ## Convexity of the finite tilted fan -/

theorem facetValue_combo {N : Nat} (u v : Fin N → ℝ)
    (s : FacetIndex N) (a b : ℝ) (hab : a + b = 1) :
    facetValue (a • u + b • v) s =
      a * facetValue u s + b * facetValue v s := by
  cases s with
  | none => simp
  | some j =>
      simp only [facetValue_some, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hc : intercept N j =
          a * intercept N j + b * intercept N j := by
        calc
          intercept N j = (a + b) * intercept N j := by rw [hab, one_mul]
          _ = a * intercept N j + b * intercept N j := by ring
      nth_rewrite 1 [hc]
      ring

/-- A finite maximum of the affine facets is convex, proved directly from an
active facet at the interpolation point. -/
theorem phi_convexOn {N : Nat} :
    ConvexOn ℝ Set.univ (@phi N) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  obtain ⟨s, hs⟩ := exists_activeFacet (a • u + b • v)
  change phi (a • u + b • v) ≤ a • phi u + b • phi v
  rw [← hs, facetValue_combo u v s a b hab]
  simp only [smul_eq_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (facetValue_le_phi u s) ha)
    (mul_le_mul_of_nonneg_left (facetValue_le_phi v s) hb)

/-! ## Convexification of one progress block -/

/-- The exact corrected progress block used in the weak-convexity proof. -/
def correctedNegPsi {N : Nat} (u : Fin N → ℝ) : ℝ :=
  -psi u + (3 * (N : ℝ) / 16) * WeaklyConvexLowerBound.Foundation.vecSq u

theorem correctedNegPsi_eq_sum {N : Nat} (hN : 0 < N)
    (u : Fin N → ℝ) :
    correctedNegPsi u =
      (1 / (N : ℝ)) * ∑ j, qConvexified ((N : ℝ) * u j / 4) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold correctedNegPsi psi qConvexified
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  have hneg :
      (∑ j : Fin N, -(q ((N : ℝ) * u j / 4)) / (N : ℝ)) =
        -((∑ j : Fin N, q ((N : ℝ) * u j / 4)) / (N : ℝ)) := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  have hquad :
      (∑ j : Fin N, 3 * (N : ℝ) / 16 * u j ^ 2) =
        3 * (N : ℝ) / 16 * ∑ j : Fin N, u j ^ 2 := by
    rw [Finset.mul_sum]
  calc
    -((∑ j, q ((N : ℝ) * u j / 4)) / (N : ℝ)) +
          3 * (N : ℝ) / 16 * ∑ j, u j ^ 2 =
        ∑ j, (-(q ((N : ℝ) * u j / 4)) / (N : ℝ) +
          3 * (N : ℝ) / 16 * u j ^ 2) := by
      rw [Finset.sum_add_distrib]
      rw [hneg, hquad]
    _ = ∑ j, (1 / (N : ℝ)) *
          (-q ((N : ℝ) * u j / 4) +
            3 * ((N : ℝ) * u j / 4) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp [hNR]
      ring
    _ = (1 / (N : ℝ)) * ∑ j,
          (-q ((N : ℝ) * u j / 4) +
            3 * ((N : ℝ) * u j / 4) ^ 2) := by
      rw [Finset.mul_sum]

/-- The sharp block statement behind `Lip(∇ψ) ≤ 3N/8`: the function
`-ψ + (3N/16)‖·‖²` is convex. -/
theorem correctedNegPsi_convexOn {N : Nat} (hN : 0 < N) :
    ConvexOn ℝ Set.univ (@correctedNegPsi N) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  rw [correctedNegPsi_eq_sum hN, correctedNegPsi_eq_sum hN,
    correctedNegPsi_eq_sum hN]
  have hNR : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  simp only [smul_eq_mul]
  rw [show a * (1 / (N : ℝ) * ∑ j, qConvexified ((N : ℝ) * u j / 4)) +
      b * (1 / (N : ℝ) * ∑ j, qConvexified ((N : ℝ) * v j / 4)) =
      (1 / (N : ℝ)) *
        (a * ∑ j, qConvexified ((N : ℝ) * u j / 4) +
          b * ∑ j, qConvexified ((N : ℝ) * v j / 4)) by ring]
  apply mul_le_mul_of_nonneg_left _ hNR
  calc
    (∑ j, qConvexified ((N : ℝ) * (a • u + b • v) j / 4)) ≤
        ∑ j, (a * qConvexified ((N : ℝ) * u j / 4) +
          b * qConvexified ((N : ℝ) * v j / 4)) := by
      apply Finset.sum_le_sum
      intro j _
      have hscalar := qConvexified_convexOn.2
        (Set.mem_univ ((N : ℝ) * u j / 4))
        (Set.mem_univ ((N : ℝ) * v j / 4)) ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hscalar ⊢
      convert hscalar using 1 <;> ring
    _ = a * ∑ j, qConvexified ((N : ℝ) * u j / 4) +
        b * ∑ j, qConvexified ((N : ℝ) * v j / 4) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ## Euclidean difference bounds -/

theorem coordinate_sq_le_vecSq {N : Nat} (u : Fin N → ℝ) (j : Fin N) :
    u j ^ 2 ≤ WeaklyConvexLowerBound.Foundation.vecSq u := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (u i)) (Finset.mem_univ j)

theorem coordinate_abs_le_sqrt_vecSq {N : Nat} (u : Fin N → ℝ)
    (j : Fin N) :
    |u j| ≤ Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq u) := by
  have h := Real.sqrt_le_sqrt (coordinate_sq_le_vecSq u j)
  simpa [Real.sqrt_sq_eq_abs] using h

/-- One-sided fan difference bound obtained by selecting an active facet at
the first argument. -/
theorem phi_sub_le_scaled_coord_abs {N : Nat} (hN : 0 < N)
    (u v : Fin N → ℝ) :
    ∃ j : Fin N, phi u - phi v ≤
      ((N : ℝ) / 8) * |u j - v j| := by
  obtain ⟨s, hs⟩ := exists_activeFacet u
  cases s with
  | none =>
      refine ⟨firstCoord hN, ?_⟩
      have hphi0 : phi u = 0 := by simpa [ActiveFacet] using hs.symm
      rw [hphi0]
      have hleft : -phi v ≤ 0 := neg_nonpos.mpr (phi_nonneg v)
      have hc : (0 : ℝ) ≤ (N : ℝ) / 8 :=
        div_nonneg (Nat.cast_nonneg N) (show (0 : ℝ) ≤ 8 by norm_num)
      have ha : (0 : ℝ) ≤ |u (firstCoord hN) - v (firstCoord hN)| :=
        abs_nonneg _
      simpa only [zero_sub] using hleft.trans (mul_nonneg hc ha)
  | some j =>
      refine ⟨j, ?_⟩
      have hfacet : facetValue v (some j) ≤ phi v := facetValue_le_phi v _
      have hone : phi u - phi v ≤
          facetValue u (some j) - facetValue v (some j) := by
        rw [← hs]
        linarith
      calc
        phi u - phi v ≤
            facetValue u (some j) - facetValue v (some j) := hone
        _ = -((N : ℝ) / 8) * (u j - v j) := by
          simp only [facetValue_some]
          ring
        _ ≤ ((N : ℝ) / 8) * |u j - v j| := by
          have hc : (0 : ℝ) ≤ (N : ℝ) / 8 :=
            div_nonneg (Nat.cast_nonneg _) (show (0 : ℝ) ≤ 8 by norm_num)
          have habs : -(u j - v j) ≤ |u j - v j| := neg_le_abs _
          nlinarith

theorem phi_abs_sub_le_sqrt {N : Nat} (hN : 0 < N)
    (u v : Fin N → ℝ) :
    |phi u - phi v| ≤
      ((N : ℝ) / 8) *
        Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v)) := by
  obtain ⟨j, huv⟩ := phi_sub_le_scaled_coord_abs hN u v
  obtain ⟨k, hvu⟩ := phi_sub_le_scaled_coord_abs hN v u
  have hc : (0 : ℝ) ≤ (N : ℝ) / 8 :=
    div_nonneg (Nat.cast_nonneg _) (show (0 : ℝ) ≤ 8 by norm_num)
  have hj := coordinate_abs_le_sqrt_vecSq (u - v) j
  have hk := coordinate_abs_le_sqrt_vecSq (u - v) k
  simp only [Pi.sub_apply] at hj hk
  have hupper : phi u - phi v ≤
      ((N : ℝ) / 8) *
        Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v)) :=
    huv.trans (mul_le_mul_of_nonneg_left hj hc)
  have hvu' : phi v - phi u ≤ ((N : ℝ) / 8) * |u k - v k| := by
    simpa [abs_sub_comm] using hvu
  have hlower : -(((N : ℝ) / 8) *
        Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v))) ≤
      phi u - phi v := by
    have h := hvu'.trans (mul_le_mul_of_nonneg_left hk hc)
    linarith
  exact (abs_le.2 ⟨hlower, hupper⟩)

/-- Squared Euclidean Lipschitz certificate for the tilted max-affine fan. -/
theorem phi_sub_sq_le {N : Nat} (hN : 0 < N) (u v : Fin N → ℝ) :
    (phi u - phi v) ^ 2 ≤
      ((N : ℝ) ^ 2 / 64) *
        WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
  have habs := phi_abs_sub_le_sqrt hN u v
  have hs0 : 0 ≤ WeaklyConvexLowerBound.Foundation.vecSq (u - v) :=
    WeaklyConvexLowerBound.Foundation.vecSq_nonneg _
  have hr0 := Real.sqrt_nonneg (WeaklyConvexLowerBound.Foundation.vecSq (u - v))
  have hc0 : (0 : ℝ) ≤ (N : ℝ) / 8 :=
    div_nonneg (Nat.cast_nonneg _) (show (0 : ℝ) ≤ 8 by norm_num)
  have hright0 : (0 : ℝ) ≤ (N : ℝ) / 8 *
      Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v)) :=
    mul_nonneg hc0 hr0
  have hsquare : |phi u - phi v| ^ 2 ≤
      (((N : ℝ) / 8) *
        Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v))) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) hright0).2 habs
  calc
    (phi u - phi v) ^ 2 = |phi u - phi v| ^ 2 := by rw [sq_abs]
    _ ≤ (((N : ℝ) / 8) *
        Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq (u - v))) ^ 2 := hsquare
    _ = ((N : ℝ) ^ 2 / 64) *
        WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
      rw [mul_pow, Real.sq_sqrt hs0]
      ring

theorem q_scaled_abs_sub_le {N : Nat} (u v : Fin N → ℝ) (j : Fin N) :
    |q ((N : ℝ) * u j / 4) - q ((N : ℝ) * v j / 4)| ≤
      (3 * (N : ℝ) / 8) * |u j - v j| := by
  have h := q_abs_sub_le ((N : ℝ) * u j / 4) ((N : ℝ) * v j / 4)
  have hscale :
      |(N : ℝ) * u j / 4 - (N : ℝ) * v j / 4| =
        ((N : ℝ) / 4) * |u j - v j| := by
    rw [show (N : ℝ) * u j / 4 - (N : ℝ) * v j / 4 =
      ((N : ℝ) / 4) * (u j - v j) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 4)]
  rw [hscale] at h
  convert h using 1 <;> ring

theorem q_scaled_sub_sq_le {N : Nat} (u v : Fin N → ℝ) (j : Fin N) :
    (q ((N : ℝ) * u j / 4) - q ((N : ℝ) * v j / 4)) ^ 2 ≤
      (9 * (N : ℝ) ^ 2 / 64) * (u j - v j) ^ 2 := by
  have h := q_scaled_abs_sub_le u v j
  have hc : (0 : ℝ) ≤ 3 * (N : ℝ) / 8 := by positivity
  have hs :
      (q ((N : ℝ) * u j / 4) - q ((N : ℝ) * v j / 4)) ^ 2 ≤
        ((3 * (N : ℝ) / 8) * (u j - v j)) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_mul, abs_of_nonneg hc] using h
  calc
    _ ≤ ((3 * (N : ℝ) / 8) * (u j - v j)) ^ 2 := hs
    _ = (9 * (N : ℝ) ^ 2 / 64) * (u j - v j) ^ 2 := by ring

theorem psi_sub_eq_sum_scaled_sub {N : Nat} (u v : Fin N → ℝ) :
    psi u - psi v =
      (∑ j, (q ((N : ℝ) * u j / 4) -
        q ((N : ℝ) * v j / 4))) / (N : ℝ) := by
  unfold psi
  rw [Finset.sum_sub_distrib]
  ring

/-- Function-value Lipschitz estimate for one progress block, in the exact
squared Euclidean geometry needed when the blocks are assembled. -/
theorem psi_sub_sq_le {N : Nat} (hN : 0 < N) (u v : Fin N → ℝ) :
    (psi u - psi v) ^ 2 ≤
      (9 * (N : ℝ) / 64) *
        WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
  let d : Fin N → ℝ := fun j ↦
    q ((N : ℝ) * u j / 4) - q ((N : ℝ) * v j / 4)
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin N))) (f := d)
  have hcoords :
      (∑ j, d j ^ 2) ≤
        (9 * (N : ℝ) ^ 2 / 64) *
          WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
    unfold WeaklyConvexLowerBound.Foundation.vecSq
    change (∑ j, d j ^ 2) ≤
      (9 * (N : ℝ) ^ 2 / 64) * ∑ j, (u j - v j) ^ 2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ q_scaled_sub_sq_le u v j
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [psi_sub_eq_sum_scaled_sub]
  change ((∑ j, d j) / (N : ℝ)) ^ 2 ≤ _
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNR)).2
  have hcs' :
      (∑ j, d j) ^ 2 ≤ (N : ℝ) * ∑ j, d j ^ 2 := by
    simpa using hcs
  have hv0 := WeaklyConvexLowerBound.Foundation.vecSq_nonneg (u - v)
  calc
    (∑ j, d j) ^ 2 ≤ (N : ℝ) * ∑ j, d j ^ 2 := hcs'
    _ ≤ (N : ℝ) *
        ((9 * (N : ℝ) ^ 2 / 64) *
          WeaklyConvexLowerBound.Foundation.vecSq (u - v)) :=
      mul_le_mul_of_nonneg_left hcoords hNR.le
    _ = (9 * (N : ℝ) / 64 *
          WeaklyConvexLowerBound.Foundation.vecSq (u - v)) * (N : ℝ) ^ 2 := by ring

/-! ## The fixed-weight variational branches -/

/-- The successor weight `w_{m+1}`, with the manuscript's convention
`w_{M+1}=0`. -/
def nextOuterWeight {M : Nat} (w : Fin M → ℝ) (m : Fin M) : ℝ :=
  if hm : m.1 + 1 < M then w ⟨m.1 + 1, hm⟩ else 0

/-- The nonnegative net progress coefficient `1-w_{m+1}`. -/
def netProgressWeight {M : Nat} (w : Fin M → ℝ) (m : Fin M) : ℝ :=
  1 - nextOuterWeight w m

theorem feasibleOuterWeight_le_one {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) : w m ≤ 1 := by
  have hmSq : (w m) ^ 2 ≤ ∑ i, (w i) ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (w i)) (Finset.mem_univ m)
  have hs : (w m) ^ 2 ≤ 1 := hmSq.trans hw.2
  nlinarith [hw.1 m]

theorem nextOuterWeight_nonneg {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) :
    0 ≤ nextOuterWeight w m := by
  unfold nextOuterWeight
  split
  · exact hw.1 _
  · exact le_rfl

theorem nextOuterWeight_le_one {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) :
    nextOuterWeight w m ≤ 1 := by
  unfold nextOuterWeight
  split
  · exact feasibleOuterWeight_le_one hw _
  · norm_num

theorem netProgressWeight_nonneg {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) :
    0 ≤ netProgressWeight w m := by
  unfold netProgressWeight
  linarith [nextOuterWeight_le_one hw m]

theorem netProgressWeight_le_one {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) :
    netProgressWeight w m ≤ 1 := by
  unfold netProgressWeight
  linarith [nextOuterWeight_nonneg hw m]

/-- Reindexing identity which turns predecessor progress in `sigmaScore`
into the net coefficients of the variational formula. -/
theorem sum_weight_mul_previousProgress {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) :
    (∑ m, w m * previousProgress z m) =
      w (firstBlock hM) + ∑ m, nextOuterWeight w m * psi (z m) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [previousProgress, firstBlock, nextOuterWeight]
  apply Finset.sum_congr rfl
  intro m _
  congr 2 <;> apply Fin.ext <;> simp

theorem outerDot_sigmaScore_eq {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) :
    outerDot w (sigmaScore z) =
      w (firstBlock hM) - (5 / 4 : ℝ) * ∑ m, w m +
        ∑ m, w m * phi (z m) +
        ∑ m, nextOuterWeight w m * psi (z m) := by
  unfold outerDot sigmaScore
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_weight_mul_previousProgress hM]
  rw [← Finset.sum_mul]
  ring

/-- The fixed-weight branch in the decomposed form used for both regularity
estimates. -/
def expandedActivationBranch {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) : ℝ :=
  (2 / (N : ℝ)) *
    (w (firstBlock hM) - (5 / 4 : ℝ) * ∑ m, w m +
      ∑ m, w m * phi (z m) -
      ∑ m, netProgressWeight w m * psi (z m))

theorem activationBranch_eq_expanded {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) :
    activationBranch w z = expandedActivationBranch hM w z := by
  unfold activationBranch expandedActivationBranch
  rw [outerDot_sigmaScore_eq hM]
  have hprogress :
      (∑ m, nextOuterWeight w m * psi (z m)) - ∑ m, psi (z m) =
        -∑ m, netProgressWeight w m * psi (z m) := by
    unfold netProgressWeight
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [show w (firstBlock hM) - 5 / 4 * ∑ m, w m +
        ∑ m, w m * phi (z m) +
        ∑ m, nextOuterWeight w m * psi (z m) - ∑ m, psi (z m) =
      w (firstBlock hM) - 5 / 4 * ∑ m, w m +
        ∑ m, w m * phi (z m) -
        ∑ m, netProgressWeight w m * psi (z m) by
    rw [show w (firstBlock hM) - 5 / 4 * ∑ m, w m +
        ∑ m, w m * phi (z m) +
        ∑ m, nextOuterWeight w m * psi (z m) - ∑ m, psi (z m) =
      w (firstBlock hM) - 5 / 4 * ∑ m, w m +
        ∑ m, w m * phi (z m) +
        ((∑ m, nextOuterWeight w m * psi (z m)) - ∑ m, psi (z m)) by ring,
      hprogress]
    ring]

theorem blockSq_eq_sum_vecSq {M N : Nat} (z : BlockVec M N) :
    blockSq z = ∑ m, WeaklyConvexLowerBound.Foundation.vecSq (z m) := by
  rfl

def branchFanDifference {M N : Nat} (w : Fin M → ℝ)
    (x y : BlockVec M N) : ℝ :=
  (2 / (N : ℝ)) * ∑ m, w m * (phi (x m) - phi (y m))

def branchProgressDifference {M N : Nat} (w : Fin M → ℝ)
    (x y : BlockVec M N) : ℝ :=
  (2 / (N : ℝ)) * ∑ m,
    netProgressWeight w m * (psi (x m) - psi (y m))

theorem activationBranch_sub_eq {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (x y : BlockVec M N) :
    activationBranch w x - activationBranch w y =
      branchFanDifference w x y - branchProgressDifference w x y := by
  rw [activationBranch_eq_expanded hM, activationBranch_eq_expanded hM]
  unfold expandedActivationBranch branchFanDifference branchProgressDifference
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

theorem branchFanDifference_sq_le {M N : Nat} (hN : 0 < N)
    {w : Fin M → ℝ} (hw : FeasibleOuterWeight w)
    (x y : BlockVec M N) :
    (branchFanDifference w x y) ^ 2 ≤ (1 / 16 : ℝ) * blockSq (x - y) := by
  let d : Fin M → ℝ := fun m ↦ phi (x m) - phi (y m)
  let r : Fin M → ℝ := fun m ↦ w m * d m
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin M))
    (r := r) (f := fun m ↦ (w m) ^ 2) (g := fun m ↦ (d m) ^ 2)
    (fun m _ ↦ sq_nonneg _) (fun m _ ↦ sq_nonneg _)
    (fun m _ ↦ by
      change (w m * d m) ^ 2 ≤ (w m) ^ 2 * (d m) ^ 2
      rw [mul_pow])
  have hdsum : (∑ m, (d m) ^ 2) ≤
      ((N : ℝ) ^ 2 / 64) * blockSq (x - y) := by
    rw [blockSq_eq_sum_vecSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    simpa [d] using phi_sub_sq_le hN (x m) (y m)
  have hd0 : 0 ≤ ∑ m, (d m) ^ 2 :=
    Finset.sum_nonneg fun m _ ↦ sq_nonneg _
  have htarget0 : 0 ≤ ((N : ℝ) ^ 2 / 64) * blockSq (x - y) :=
    mul_nonneg (by positivity) (blockSq_nonneg _)
  have hprod :
      (∑ m, (w m) ^ 2) * ∑ m, (d m) ^ 2 ≤
        ((N : ℝ) ^ 2 / 64) * blockSq (x - y) := by
    calc
      _ ≤ 1 * ∑ m, (d m) ^ 2 :=
        mul_le_mul hw.2 le_rfl hd0 (by norm_num)
      _ ≤ 1 * (((N : ℝ) ^ 2 / 64) * blockSq (x - y)) :=
        mul_le_mul_of_nonneg_left hdsum (by norm_num)
      _ = _ := one_mul _
  have hraw : (∑ m, r m) ^ 2 ≤
      ((N : ℝ) ^ 2 / 64) * blockSq (x - y) := hcs.trans hprod
  have hscale0 : 0 ≤ (2 / (N : ℝ)) ^ 2 := sq_nonneg _
  unfold branchFanDifference
  change ((2 / (N : ℝ)) * ∑ m, r m) ^ 2 ≤ _
  calc
    _ = (2 / (N : ℝ)) ^ 2 * (∑ m, r m) ^ 2 := by ring
    _ ≤ (2 / (N : ℝ)) ^ 2 *
        (((N : ℝ) ^ 2 / 64) * blockSq (x - y)) :=
      mul_le_mul_of_nonneg_left hraw hscale0
    _ = (1 / 16 : ℝ) * blockSq (x - y) := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNR]
      ring

theorem branchProgressDifference_sq_le {M N : Nat} (hN : 0 < N)
    {w : Fin M → ℝ} (hw : FeasibleOuterWeight w)
    (x y : BlockVec M N) :
    (branchProgressDifference w x y) ^ 2 ≤
      (9 * (M : ℝ) / (16 * (N : ℝ))) * blockSq (x - y) := by
  let a : Fin M → ℝ := netProgressWeight w
  let d : Fin M → ℝ := fun m ↦ psi (x m) - psi (y m)
  let r : Fin M → ℝ := fun m ↦ a m * d m
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin M))
    (r := r) (f := fun m ↦ (a m) ^ 2) (g := fun m ↦ (d m) ^ 2)
    (fun m _ ↦ sq_nonneg _) (fun m _ ↦ sq_nonneg _)
    (fun m _ ↦ by
      change (a m * d m) ^ 2 ≤ (a m) ^ 2 * (d m) ^ 2
      rw [mul_pow])
  have hasq (m : Fin M) : (a m) ^ 2 ≤ 1 := by
    have ha0 : 0 ≤ a m := netProgressWeight_nonneg hw m
    have ha1 : a m ≤ 1 := netProgressWeight_le_one hw m
    nlinarith
  have hasum : (∑ m, (a m) ^ 2) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ _m : Fin M, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ ↦ hasq m
      _ = (M : ℝ) := by simp
  have hdsum : (∑ m, (d m) ^ 2) ≤
      (9 * (N : ℝ) / 64) * blockSq (x - y) := by
    rw [blockSq_eq_sum_vecSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    simpa [d] using psi_sub_sq_le hN (x m) (y m)
  have ha0 : 0 ≤ ∑ m, (a m) ^ 2 :=
    Finset.sum_nonneg fun m _ ↦ sq_nonneg _
  have hd0 : 0 ≤ ∑ m, (d m) ^ 2 :=
    Finset.sum_nonneg fun m _ ↦ sq_nonneg _
  have htarget0 : 0 ≤ (9 * (N : ℝ) / 64) * blockSq (x - y) :=
    mul_nonneg (by positivity) (blockSq_nonneg _)
  have hprod :
      (∑ m, (a m) ^ 2) * ∑ m, (d m) ^ 2 ≤
        (M : ℝ) * ((9 * (N : ℝ) / 64) * blockSq (x - y)) :=
    mul_le_mul hasum hdsum hd0 (Nat.cast_nonneg M)
  have hraw : (∑ m, r m) ^ 2 ≤
      (M : ℝ) * ((9 * (N : ℝ) / 64) * blockSq (x - y)) :=
    hcs.trans hprod
  have hscale0 : 0 ≤ (2 / (N : ℝ)) ^ 2 := sq_nonneg _
  unfold branchProgressDifference
  change ((2 / (N : ℝ)) * ∑ m, r m) ^ 2 ≤ _
  calc
    _ = (2 / (N : ℝ)) ^ 2 * (∑ m, r m) ^ 2 := by ring
    _ ≤ (2 / (N : ℝ)) ^ 2 *
        ((M : ℝ) * ((9 * (N : ℝ) / 64) * blockSq (x - y))) :=
      mul_le_mul_of_nonneg_left hraw hscale0
    _ = (9 * (M : ℝ) / (16 * (N : ℝ))) * blockSq (x - y) := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNR]
      ring

/-- Uniform Euclidean Lipschitz bound for every feasible variational branch.
The proof deliberately keeps the stronger squared constant `7/32`. -/
theorem activationBranch_sub_sq_le {M N : Nat} (hA : Admissible M N)
    {w : Fin M → ℝ} (hw : FeasibleOuterWeight w)
    (x y : BlockVec M N) :
    (activationBranch w x - activationBranch w y) ^ 2 ≤
      (7 / 32 : ℝ) * blockSq (x - y) := by
  rw [activationBranch_sub_eq hA.M_pos]
  have hfan := branchFanDifference_sq_le hA.N_pos hw x y
  have hprog := branchProgressDifference_sq_le hA.N_pos hw x y
  have hMN : (M : ℝ) ≤ (N : ℝ) / 12 := by
    have hcast : (12 : ℝ) * M ≤ (N : ℝ) := by
      exact_mod_cast hA.twelve_M_le
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
  have hprog' : (branchProgressDifference w x y) ^ 2 ≤
      (3 / 64 : ℝ) * blockSq (x - y) := by
    have hcoeff : 9 * (M : ℝ) / (16 * (N : ℝ)) ≤ 3 / 64 := by
      apply (div_le_iff₀ (show (0 : ℝ) < 16 * N by positivity)).2
      nlinarith
    exact hprog.trans (mul_le_mul_of_nonneg_right hcoeff (blockSq_nonneg _))
  nlinarith [sq_nonneg
    (branchFanDifference w x y + branchProgressDifference w x y)]

theorem blockSq_sub_comm {M N : Nat} (x y : BlockVec M N) :
    blockSq (x - y) = blockSq (y - x) := by
  unfold blockSq
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  nlinarith

theorem hardValue_sub_sq_le_strong {M N : Nat} (hA : Admissible M N)
    (x y : BlockVec M N) :
    (hardValue x - hardValue y) ^ 2 ≤
      (7 / 32 : ℝ) * blockSq (x - y) := by
  let wx : Fin M → ℝ := canonicalOuterWeight (sigmaScore x)
  let wy : Fin M → ℝ := canonicalOuterWeight (sigmaScore y)
  have hwx : FeasibleOuterWeight wx := canonicalOuterWeight_feasible _
  have hwy : FeasibleOuterWeight wy := canonicalOuterWeight_feasible _
  have hcanonx : activationBranch wx x = hardValue x := by
    simpa [wx] using activationBranch_canonical_eq_hardValue x
  have hcanony : activationBranch wy y = hardValue y := by
    simpa [wy] using activationBranch_canonical_eq_hardValue y
  by_cases hxy : hardValue y ≤ hardValue x
  · have hleY := activationBranch_le_hardValue hA.N_pos hwx y
    have hone : hardValue x - hardValue y ≤
        activationBranch wx x - activationBranch wx y := by
      rw [hcanonx]
      linarith
    have hzero : 0 ≤ activationBranch wx x - activationBranch wx y := by
      linarith
    have hbranch := activationBranch_sub_sq_le hA hwx x y
    nlinarith
  · have hyx : hardValue x ≤ hardValue y := le_of_not_ge hxy
    have hleX := activationBranch_le_hardValue hA.N_pos hwy x
    have hone : hardValue y - hardValue x ≤
        activationBranch wy y - activationBranch wy x := by
      rw [hcanony]
      linarith
    have hzero : 0 ≤ activationBranch wy y - activationBranch wy x := by
      linarith
    have hbranch := activationBranch_sub_sq_le hA hwy y x
    rw [← blockSq_sub_comm x y] at hbranch
    nlinarith

/-- The concrete normalized hard function is globally one-Lipschitz in the
paper's Euclidean geometry (in fact its squared constant is at most `7/32`). -/
theorem hardValue_euclideanLipschitz {M N : Nat} (hA : Admissible M N) :
    EuclideanLipschitz 1 (@hardValue M N) := by
  intro x y
  have h := hardValue_sub_sq_le_strong hA x y
  have hs := blockSq_nonneg (x - y)
  norm_num
  nlinarith

/-! ## Weak convexity of fixed branches -/

theorem phi_weighted_sum_convexOn {M N : Nat} {w : Fin M → ℝ}
    (hw : ∀ m, 0 ≤ w m) :
    ConvexOn ℝ Set.univ (fun z : BlockVec M N ↦ ∑ m, w m * phi (z m)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ m, w m * phi (a • x m + b • y m)) ≤
        ∑ m, w m * (a * phi (x m) + b * phi (y m)) := by
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_left _ (hw m)
      simpa only [smul_eq_mul] using
        phi_convexOn.2 (Set.mem_univ (x m)) (Set.mem_univ (y m)) ha hb hab
    _ = a * ∑ m, w m * phi (x m) +
        b * ∑ m, w m * phi (y m) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun p q : ℝ ↦ p + q)
      · apply Finset.sum_congr rfl
        intro m _
        ring
      · apply Finset.sum_congr rfl
        intro m _
        ring

theorem correctedNegPsi_weighted_sum_convexOn {M N : Nat} (hN : 0 < N)
    {c : Fin M → ℝ} (hc : ∀ m, 0 ≤ c m) :
    ConvexOn ℝ Set.univ
      (fun z : BlockVec M N ↦ ∑ m, c m * correctedNegPsi (z m)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ m, c m * correctedNegPsi (a • x m + b • y m)) ≤
        ∑ m, c m *
          (a * correctedNegPsi (x m) + b * correctedNegPsi (y m)) := by
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_left _ (hc m)
      simpa only [smul_eq_mul] using
        (correctedNegPsi_convexOn hN).2
          (Set.mem_univ (x m)) (Set.mem_univ (y m)) ha hb hab
    _ = a * ∑ m, c m * correctedNegPsi (x m) +
        b * ∑ m, c m * correctedNegPsi (y m) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun p q : ℝ ↦ p + q)
      · apply Finset.sum_congr rfl
        intro m _
        ring
      · apply Finset.sum_congr rfl
        intro m _
        ring

def weightedBlockSq {M N : Nat} (c : Fin M → ℝ)
    (z : BlockVec M N) : ℝ :=
  ∑ m, c m * WeaklyConvexLowerBound.Foundation.vecSq (z m)

private theorem sq_combo_le (a b s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (a * s + b * t) ^ 2 ≤ a * s ^ 2 + b * t ^ 2 := by
  have hp : 0 ≤ a * b * (s - t) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  nlinarith

theorem weightedBlockSq_convexOn {M N : Nat} {c : Fin M → ℝ}
    (hc : ∀ m, 0 ≤ c m) :
    ConvexOn ℝ Set.univ (@weightedBlockSq M N c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  unfold weightedBlockSq WeaklyConvexLowerBound.Foundation.vecSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ m, c m * ∑ j, (a * x m j + b * y m j) ^ 2) ≤
        ∑ m, c m * ∑ j, (a * (x m j) ^ 2 + b * (y m j) ^ 2) := by
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_left _ (hc m)
      exact Finset.sum_le_sum fun j _ ↦ sq_combo_le a b (x m j) (y m j) ha hb hab
    _ = ∑ m, ((∑ j, a * (c m * (x m j) ^ 2)) +
        ∑ j, b * (c m * (y m j) ^ 2)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ m, ∑ j, a * (c m * (x m j) ^ 2)) +
        ∑ m, ∑ j, b * (c m * (y m j) ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ = a * ∑ m, c m * ∑ j, (x m j) ^ 2 +
        b * ∑ m, c m * ∑ j, (y m j) ^ 2 := by
      simp_rw [Finset.mul_sum]

theorem weightedBlockSq_net_add_next {M N : Nat} (w : Fin M → ℝ)
    (z : BlockVec M N) :
    weightedBlockSq (netProgressWeight w) z +
      weightedBlockSq (nextOuterWeight w) z = blockSq z := by
  unfold weightedBlockSq netProgressWeight
  rw [blockSq_eq_sum_vecSq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem scaled_correctedNegPsi_sum_eq {M N : Nat} (hN : 0 < N)
    (c : Fin M → ℝ) (z : BlockVec M N) :
    (2 / (N : ℝ)) * ∑ m, c m * correctedNegPsi (z m) =
      -(2 / (N : ℝ)) * ∑ m, c m * psi (z m) +
        (3 / 8 : ℝ) * weightedBlockSq c z := by
  have hneg :
      (∑ m, c m * (-psi (z m))) = -∑ m, c m * psi (z m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hquad :
      (∑ m, c m * ((3 * (N : ℝ) / 16) *
        WeaklyConvexLowerBound.Foundation.vecSq (z m))) =
      (3 * (N : ℝ) / 16) * weightedBlockSq c z := by
    unfold weightedBlockSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp_rw [correctedNegPsi, mul_add]
  rw [Finset.sum_add_distrib, hneg, hquad]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNR]
  ring

/-- A branch after adding the common `3/8` quadratic correction, written as
a sum of manifestly convex terms. -/
def convexifiedActivationBranch {M N : Nat} (hM : 0 < M)
    (w : Fin M → ℝ) (z : BlockVec M N) : ℝ :=
  (2 / (N : ℝ)) *
      (w (firstBlock hM) - (5 / 4 : ℝ) * ∑ m, w m) +
    (2 / (N : ℝ)) * ∑ m, w m * phi (z m) +
    (2 / (N : ℝ)) *
      ∑ m, netProgressWeight w m * correctedNegPsi (z m) +
    (3 / 8 : ℝ) * weightedBlockSq (nextOuterWeight w) z

theorem activationBranch_add_three_eighths_eq {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) (w : Fin M → ℝ)
    (z : BlockVec M N) :
    activationBranch w z + (3 / 8 : ℝ) * blockSq z =
      convexifiedActivationBranch hM w z := by
  rw [activationBranch_eq_expanded hM]
  unfold expandedActivationBranch convexifiedActivationBranch
  rw [scaled_correctedNegPsi_sum_eq hN]
  have hsq := weightedBlockSq_net_add_next w z
  ring_nf at hsq ⊢
  linarith

theorem convexifiedActivationBranch_convexOn {M N : Nat}
    (hA : Admissible M N) {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) :
    ConvexOn ℝ Set.univ
      (@convexifiedActivationBranch M N hA.M_pos w) := by
  let C : ℝ := (2 / (N : ℝ)) *
    (w (firstBlock hA.M_pos) - (5 / 4 : ℝ) * ∑ m, w m)
  let fan : BlockVec M N → ℝ := fun z ↦ ∑ m, w m * phi (z m)
  let prog : BlockVec M N → ℝ := fun z ↦
    ∑ m, netProgressWeight w m * correctedNegPsi (z m)
  let tailSq : BlockVec M N → ℝ :=
    weightedBlockSq (nextOuterWeight w)
  have hscale : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have hthree : (0 : ℝ) ≤ 3 / 8 := by norm_num
  have hfan : ConvexOn ℝ Set.univ fan :=
    phi_weighted_sum_convexOn hw.1
  have hprog : ConvexOn ℝ Set.univ prog :=
    correctedNegPsi_weighted_sum_convexOn hA.N_pos
      (netProgressWeight_nonneg hw)
  have htail : ConvexOn ℝ Set.univ tailSq :=
    weightedBlockSq_convexOn (nextOuterWeight_nonneg hw)
  have hfanScaled : ConvexOn ℝ Set.univ
      (fun z ↦ (2 / (N : ℝ)) * fan z) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hscale hfan
  have hprogScaled : ConvexOn ℝ Set.univ
      (fun z ↦ (2 / (N : ℝ)) * prog z) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hscale hprog
  have htailScaled : ConvexOn ℝ Set.univ
      (fun z ↦ (3 / 8 : ℝ) * tailSq z) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hthree htail
  have hsum := (hfanScaled.add hprogScaled).add htailScaled
  have htotal := hsum.add_const C
  have heq : @convexifiedActivationBranch M N hA.M_pos w =
      (((fun z ↦ (2 / (N : ℝ)) * fan z) +
          (fun z ↦ (2 / (N : ℝ)) * prog z)) +
        (fun z ↦ (3 / 8 : ℝ) * tailSq z)) + (fun _ ↦ C) := by
    funext z
    simp only [convexifiedActivationBranch, C, fan, prog, tailSq, Pi.add_apply]
    ring
  rw [heq]
  exact htotal

theorem blockSq_convexOn {M N : Nat} :
    ConvexOn ℝ Set.univ (@blockSq M N) := by
  have h := weightedBlockSq_convexOn (M := M) (N := N)
    (c := fun _ : Fin M ↦ (1 : ℝ)) (fun _ ↦ (by norm_num))
  have heq : (@weightedBlockSq M N (fun _ ↦ (1 : ℝ))) = @blockSq M N := by
    funext z
    rw [blockSq_eq_sum_vecSq]
    simp [weightedBlockSq]
  rw [← heq]
  exact h

/-- The pointwise maximum argument, with the exact canonical maximizing
weight at the interpolation point, proves the sharper `3/4` modulus. -/
theorem hardValue_three_eighths_correction_convexOn {M N : Nat}
    (hA : Admissible M N) :
    ConvexOn ℝ Set.univ
      (fun z : BlockVec M N ↦ hardValue z + (3 / 8 : ℝ) * blockSq z) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z : BlockVec M N := a • x + b • y
  let w : Fin M → ℝ := canonicalOuterWeight (sigmaScore z)
  have hw : FeasibleOuterWeight w := canonicalOuterWeight_feasible _
  have hconv := convexifiedActivationBranch_convexOn hA hw
  have hzcanon : activationBranch w z = hardValue z := by
    simpa [w, z] using activationBranch_canonical_eq_hardValue z
  have hzeq : hardValue z + (3 / 8 : ℝ) * blockSq z =
      convexifiedActivationBranch hA.M_pos w z := by
    rw [← hzcanon]
    exact activationBranch_add_three_eighths_eq hA.M_pos hA.N_pos w z
  have hxbranch := activationBranch_le_hardValue hA.N_pos hw x
  have hybranch := activationBranch_le_hardValue hA.N_pos hw y
  have hxeq := activationBranch_add_three_eighths_eq
    hA.M_pos hA.N_pos w x
  have hyeq := activationBranch_add_three_eighths_eq
    hA.M_pos hA.N_pos w y
  have hxle : convexifiedActivationBranch hA.M_pos w x ≤
      hardValue x + (3 / 8 : ℝ) * blockSq x := by
    rw [← hxeq]
    linarith
  have hyle : convexifiedActivationBranch hA.M_pos w y ≤
      hardValue y + (3 / 8 : ℝ) * blockSq y := by
    rw [← hyeq]
    linarith
  change hardValue (a • x + b • y) +
      (3 / 8 : ℝ) * blockSq (a • x + b • y) ≤
    a • (hardValue x + (3 / 8 : ℝ) * blockSq x) +
      b • (hardValue y + (3 / 8 : ℝ) * blockSq y)
  change hardValue z + (3 / 8 : ℝ) * blockSq z ≤ _
  calc
    hardValue z + (3 / 8 : ℝ) * blockSq z =
        convexifiedActivationBranch hA.M_pos w z := hzeq
    _ ≤ a • convexifiedActivationBranch hA.M_pos w x +
        b • convexifiedActivationBranch hA.M_pos w y := by
      exact hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    _ ≤ a • (hardValue x + (3 / 8 : ℝ) * blockSq x) +
        b • (hardValue y + (3 / 8 : ℝ) * blockSq y) :=
      add_le_add
        (smul_le_smul_of_nonneg_left hxle ha)
        (smul_le_smul_of_nonneg_left hyle hb)

theorem hardValue_threeQuarter_weaklyConvex {M N : Nat}
    (hA : Admissible M N) :
    WeaklyConvex (3 / 4 : ℝ) (@hardValue M N) := by
  unfold WeaklyConvex
  convert hardValue_three_eighths_correction_convexOn hA using 1
  funext z
  ring

/-- Condition (C1), weak-convexity part, for the literal hard function. -/
theorem hardValue_one_weaklyConvex {M N : Nat} (hA : Admissible M N) :
    WeaklyConvex 1 (@hardValue M N) := by
  unfold WeaklyConvex
  have hbase := hardValue_three_eighths_correction_convexOn hA
  have hextra : ConvexOn ℝ Set.univ
      (fun z : BlockVec M N ↦ (1 / 8 : ℝ) * blockSq z) := by
    simpa only [smul_eq_mul] using
      ConvexOn.smul (show (0 : ℝ) ≤ 1 / 8 by norm_num)
        (@blockSq_convexOn M N)
  have hsum := hbase.add hextra
  have heq :
      (fun z : BlockVec M N ↦ hardValue z + 1 / 2 * blockSq z) =
      ((fun z : BlockVec M N ↦ hardValue z + (3 / 8 : ℝ) * blockSq z) +
        fun z ↦ (1 / 8 : ℝ) * blockSq z) := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact hsum

theorem hardValue_finite_valued {M N : Nat} :
    ∀ z : BlockVec M N, ∃ r : ℝ, hardValue z = r := by
  intro z
  exact ⟨hardValue z, rfl⟩

/-- Complete concrete C1 package for the normalized hard instance. -/
theorem hardValue_C1 {M N : Nat} (hA : Admissible M N) :
    (∀ z : BlockVec M N, ∃ r : ℝ, hardValue z = r) ∧
      BddBelow (Set.range (@hardValue M N)) ∧
      EuclideanLipschitz 1 (@hardValue M N) ∧
      WeaklyConvex 1 (@hardValue M N) := by
  exact ⟨hardValue_finite_valued,
    hardValue_range_bddBelow hA.N_pos,
    hardValue_euclideanLipschitz hA,
    hardValue_one_weaklyConvex hA⟩

end

end WeaklyConvexLowerBound

