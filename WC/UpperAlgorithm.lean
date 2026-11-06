import WC.ProjectedSubgradient
import Mathlib.Analysis.Convex.Jensen

/-! The actual weighted inner solver and the certified descent dichotomy. -/

noncomputable section
namespace WC

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sum_inner_weights (L : ℕ) :
    (∑ k ∈ Finset.range L, ((k : ℝ) + 1)) = (L : ℝ) * (L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

def proximalInnerAverage (x : E) (ρ G : ℝ) (select : E → E) (L : ℕ) : E :=
  (Finset.range L).centerMass (fun k => (k : ℝ) + 1) (proximalInnerIterate x ρ G select)

theorem proximalInnerAverage_formula (x : E) (ρ G : ℝ) (select : E → E) (L : ℕ) :
    proximalInnerAverage x ρ G select L =
      (2 / ((L : ℝ) * (L + 1))) •
        ∑ k ∈ Finset.range L, ((k : ℝ) + 1) • proximalInnerIterate x ρ G select k := by
  unfold proximalInnerAverage Finset.centerMass
  rw [sum_inner_weights]
  congr 1
  field_simp

theorem proximalInnerIterate_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ρ G : ℝ) {select : E → E} (hselect : Measurable select) (k : ℕ) :
    Measurable (fun x => proximalInnerIterate x ρ G select k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih =>
    change Measurable (fun x => ballProject x (G / ρ)
      (proximalInnerIterate x ρ G select k - (2 / (ρ * ((k : ℝ) + 2))) •
        (select (proximalInnerIterate x ρ G select k) +
          (2 * ρ) • (proximalInnerIterate x ρ G select k - x))))
    exact (ballProject_measurable_joint (G / ρ)).comp (measurable_id.prodMk
      (ih.sub (measurable_const.smul ((hselect.comp ih).add
        (measurable_const.smul (ih.sub measurable_id))))))

theorem proximalInnerAverage_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ρ G : ℝ) {select : E → E} (hselect : Measurable select) (L : ℕ) :
    Measurable (fun x => proximalInnerAverage x ρ G select L) := by
  simp_rw [proximalInnerAverage_formula]
  apply measurable_const.smul
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.smul (proximalInnerIterate_measurable ρ G hselect k)

/-- The actual projected inner iterates achieve `18G²/(ρ(L+1))` objective error. -/
theorem proximalInnerAverage_error {ρ G : ℝ} {f : E → ℝ}
    (x p : E) (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z))
    (hp : p ∈ Metric.closedBall x (G / ρ)) {L : ℕ} (hL : 0 < L) :
    quadraticObjective ρ f x (proximalInnerAverage x ρ G select L) - quadraticObjective ρ f x p ≤
      18 * G ^ 2 / (ρ * ((L : ℝ) + 1)) := by
  let z := proximalInnerIterate x ρ G select
  let Q := quadraticObjective ρ f x
  let W : ℝ := ∑ k ∈ Finset.range L, ((k : ℝ) + 1)
  let S : ℝ := ∑ k ∈ Finset.range L, ((k : ℝ) + 1) * Q (z k)
  let C : ℝ := 9 * G ^ 2 / ρ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hWeq : W = (L : ℝ) * (L + 1) / 2 := sum_inner_weights L
  have hW : 0 < W := by rw [hWeq]; positivity
  have hQconv : ConvexOn ℝ Set.univ Q :=
    (weaklyConvex_quadratic_strong hwc x).convexOn (fun r => by dsimp; positivity)
  have hjensen := hQconv.map_centerMass_le (t := Finset.range L)
    (w := fun k => (k : ℝ) + 1) (p := z) (fun k _ => by positivity) hW
    (fun _ _ => Set.mem_univ _)
  have hjensen' : Q (proximalInnerAverage x ρ G select L) ≤ S / W := by
    simpa only [proximalInnerAverage, Finset.centerMass, smul_eq_mul, div_eq_mul_inv,
      mul_comm, Function.comp_def, S, W] using hjensen
  have hsum := proximalInnerIterate_weighted_error x p select hρ hG hlip hwc hselect hp L
  have hsum' : S - W * Q p ≤ C * L := by
    have heq : (∑ k ∈ Finset.range L, ((k : ℝ) + 1) * (Q (z k) - Q p)) = S - W * Q p := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    rw [heq] at hsum
    exact hsum
  have hJmul := (le_div_iff₀ hW).mp hjensen'
  have hrate : (Q (proximalInnerAverage x ρ G select L) - Q p) * ((L : ℝ) + 1) ≤ 2 * C := by
    have hbig : (L : ℝ) * ((Q (proximalInnerAverage x ρ G select L) - Q p) * ((L : ℝ) + 1)) ≤
        (L : ℝ) * (2 * C) := by rw [hWeq] at hJmul hsum'; nlinarith
    exact (mul_le_mul_iff_right₀ hLreal).mp hbig
  have hfinal := (le_div_iff₀ (show (0 : ℝ) < (L : ℝ) + 1 by positivity)).mpr hrate
  have hconstant : 2 * C / ((L : ℝ) + 1) = 18 * G ^ 2 / (ρ * ((L : ℝ) + 1)) := by
    dsimp [C]
    field_simp
    ring
  rw [hconstant] at hfinal
  exact hfinal

/-- The chosen inner iteration count gives the manuscript's objective and distance tolerances. -/
theorem proximalInnerAverage_tolerance {ρ G ε : ℝ} {f : E → ℝ}
    (x p : E) (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G) (hε : 0 < ε)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z))
    (hp : IsProxPoint (1 / (2 * ρ)) f x p) {L : ℕ} (hL : 0 < L)
    (hiterations : (2 : ℝ) ^ 14 * G ^ 2 ≤ (L : ℝ) * ε ^ 2) :
    quadraticObjective ρ f x (proximalInnerAverage x ρ G select L) - quadraticObjective ρ f x p ≤
      ε ^ 2 / (512 * ρ) ∧
    ‖proximalInnerAverage x ρ G select L - p‖ ≤ ε / (16 * ρ) := by
  have herror := (proximalInnerAverage_error x p select hρ hG hlip hwc hselect
    (hp.mem_proximalBall hρ hG hlip hwc) hL).trans
      (proximal_value_tolerance hρ (show (0 : ℝ) ≤ L by positivity) hiterations)
  refine ⟨herror, ?_⟩
  have hstrong := hp.strong_minimum hρ hwc (proximalInnerAverage x ρ G select L)
  simp only [proxObjective_eq_quadratic hρ.ne'] at hstrong
  apply proximal_distance_tolerance hε hρ (norm_nonneg _)
  linarith

/-- One completely implemented inner round either certifies its center or makes strict progress. -/
theorem proximalInnerRound_dichotomy [ProperSpace E] {ρ G ε : ℝ} {f : E → ℝ}
    (x : E) (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G) (hε : 0 < ε)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z)) {L : ℕ} (hL : 0 < L)
    (hiterations : (2 : ℝ) ^ 14 * G ^ 2 ≤ (L : ℝ) * ε ^ 2) :
    (‖proximalInnerAverage x ρ G select L - x‖ ≤ ε / (4 * ρ) →
      ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) x‖ ≤ 5 * ε / 8) ∧
    (ε / (4 * ρ) < ‖proximalInnerAverage x ρ G select L - x‖ →
      ε ^ 2 / (32 * ρ) < f x - f (proximalInnerAverage x ρ G select L)) := by
  let p := proximalPoint ρ f x
  let y := proximalInnerAverage x ρ G select L
  have hp := proximalPoint_spec hρ hG hlip x
  obtain ⟨hvalue, hdist⟩ := proximalInnerAverage_tolerance x p select hρ hG hε hlip hwc hselect hp hL hiterations
  constructor
  · intro hsmall
    have hgrad : ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) x‖ ≤
        2 * ρ * (‖y - x‖ + ‖y - p‖) := by
      rw [moreau_gradient_eq hρ hG hlip hwc, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show 0 < 2 * ρ by positivity)]
      have htri : ‖x - p‖ ≤ ‖y - x‖ + ‖y - p‖ := by
        simpa only [sub_add_sub_cancel, norm_sub_rev x y] using norm_add_le (x - y) (y - p)
      exact mul_le_mul_of_nonneg_left htri (by positivity)
    exact certified_center_bound hρ hsmall hdist hgrad
  · intro hlarge
    have hdescent : quadraticObjective ρ f x p ≤ f x := by
      have h := hp x
      simpa only [proxObjective_half_inv, quadraticObjective, sub_self, norm_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] using h
    have hdec : ρ * ‖y - x‖ ^ 2 - ε ^ 2 / (512 * ρ) ≤ f x - f y := by
      change quadraticObjective ρ f x y - quadraticObjective ρ f x p ≤ _ at hvalue
      dsimp [quadraticObjective] at hvalue hdescent
      rw [norm_sub_rev x y] at hvalue
      linarith
    exact unsuccessful_round_descent hε hρ hlarge hdec

def proximalOuterUpdate (ρ G ε : ℝ) (select : E → E) (L : ℕ) (x : E) : E :=
  let y := proximalInnerAverage x ρ G select L
  if ‖y - x‖ ≤ ε / (4 * ρ) then x else y

theorem proximalOuterUpdate_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ρ G ε : ℝ) {select : E → E}
    (hselect : Measurable select) (L : ℕ) : Measurable (proximalOuterUpdate ρ G ε select L) := by
  unfold proximalOuterUpdate
  have hy := proximalInnerAverage_measurable ρ G hselect L
  exact measurable_id.ite (measurableSet_le (hy.sub measurable_id).norm measurable_const) hy

end WC
