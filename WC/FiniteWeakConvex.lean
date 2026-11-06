import WC.Oracle
import WC.Moreau
import WC.CoupledCurvature

/-! Proximal attainment and the genuine Moreau derivative for every
everywhere finite weakly convex function in finite dimension. No global
Lipschitz assumption is used. -/

noncomputable section
namespace WC
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem finite_weakSubgradient_nonempty {ρ : ℝ} {f : E → ℝ}
    (hf : WeaklyConvex ρ f) (x : E) : ∃ v, WeakSubgradient ρ f x v := by
  have hc : Continuous (fun y : E => f y + ρ / 2 * ‖y‖ ^ 2) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hf)
  obtain ⟨w, hw⟩ := continuous_convex_has_subgradient hf hc x
  refine ⟨w - ρ • x, weakSubgradient_iff_convexification.mpr ?_⟩
  simpa only [sub_add_cancel] using hw

omit [CompleteSpace E] in
theorem finite_quadraticObjective_continuous {ρ : ℝ} {f : E → ℝ}
    (hf : WeaklyConvex ρ f) (x : E) : Continuous (quadraticObjective ρ f x) :=
  (weaklyConvex_continuous hf).add (continuous_const.mul
    ((continuous_const.sub continuous_id).norm.pow 2))

theorem finite_exists_quadraticMinimizer {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : E) :
    ∃ p, IsQuadraticMinimizer ρ f x p := by
  obtain ⟨v, hv⟩ := finite_weakSubgradient_nonempty hf x
  let R : ℝ := 2 * ‖v‖ / ρ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx : x ∈ Metric.closedBall x R := by simp [hR]
  obtain ⟨p, _, hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, hx⟩ (finite_quadraticObjective_continuous hf x).continuousOn
  refine ⟨p, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall x R
  · exact hmin hy
  · have hd : R < ‖y - x‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hy
    have hvd : ‖v‖ ≤ ρ / 2 * ‖y - x‖ := by
      have ht := mul_lt_mul_of_pos_left hd hρ
      dsimp only [R] at ht
      have heq : ρ * (2 * ‖v‖ / ρ + 1) = 2 * ‖v‖ + ρ := by field_simp
      rw [heq] at ht
      linarith
    have hs := hv y
    have hi : -‖v‖ * ‖y - x‖ ≤ inner ℝ v (y - x) := by
      have h := real_inner_le_norm (-v) (y - x)
      simp only [inner_neg_left, norm_neg] at h
      linarith
    have hm := mul_le_mul_of_nonneg_right hvd (norm_nonneg (y - x))
    have hcenter : quadraticObjective ρ f x x ≤ quadraticObjective ρ f x y := by
      simp only [quadraticObjective, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, add_zero]
      rw [norm_sub_rev x y]
      nlinarith
    exact (hmin hx).trans hcenter

theorem finite_proximalPoint_spec {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : E) :
    IsProxPoint (1 / (2 * ρ)) f x (proximalPoint ρ f x) := by
  have hex : ∃ p, IsProxPoint (1 / (2 * ρ)) f x p := by
    obtain ⟨p, hp⟩ := finite_exists_quadraticMinimizer hρ hf x
    exact ⟨p, fun y => by simpa only [proxObjective_eq_quadratic hρ.ne'] using hp y⟩
  simp only [proximalPoint, dif_pos hex]
  exact Classical.choose_spec hex

theorem finite_moreau_hasGradientAt {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : E) :
    HasGradientAt (moreauEnvelope (1 / (2 * ρ)) f)
      ((2 * ρ) • (x - proximalPoint ρ f x)) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hb :
      (fun h : E => moreauEnvelope (1 / (2 * ρ)) f (x + h) -
        moreauEnvelope (1 / (2 * ρ)) f x -
        inner ℝ ((2 * ρ) • (x - proximalPoint ρ f x)) h) =O[𝓝 0]
        (fun h : E => ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (5 * ρ)
    apply Filter.Eventually.of_forall
    intro h
    have hbound := envelope_expansion_bound hρ hf
      (finite_proximalPoint_spec hρ hf x) (finite_proximalPoint_spec hρ hf (x + h))
    simpa only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using hbound
  exact hb.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

theorem finite_moreau_gradient_eq {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : E) :
    gradient (moreauEnvelope (1 / (2 * ρ)) f) x =
      (2 * ρ) • (x - proximalPoint ρ f x) :=
  (finite_moreau_hasGradientAt hρ hf x).gradient

end WC
