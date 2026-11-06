import WC.Majorant
import WC.Proximal

/-! Weak convexity and actual source attainment for the supremal majorant. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weaklyConvex_translate_sub {ρ c : ℝ} {f : E → ℝ}
    (hf : WeaklyConvex ρ f) (v : E) :
    WeaklyConvex ρ (fun x => f (x + v) - c) := by
  have htr : ConvexOn ℝ Set.univ (fun x : E => f (x + v) + ρ / 2 * ‖x + v‖ ^ 2) := by
    simpa only [Set.preimage_univ, Function.comp_def, add_comm v] using hf.translate_right v
  let C : ℝ := -ρ / 2 * ‖v‖ ^ 2 - c
  have haff : ConvexOn ℝ Set.univ (fun x : E => -ρ * inner ℝ v x + C) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    have hconst : (a + b) * C = C := by rw [hab, one_mul]
    nlinarith
  apply (htr.add haff).congr
  intro x _
  dsimp [C]
  rw [norm_add_sq_real, real_inner_comm x v]
  ring

/-- The translated supremum genuinely preserves the weak-convexity modulus. -/
theorem majorant_weaklyConvex {ρ L : ℝ} {f : E → ℝ}
    (hfinite : MajorantFinite f L) (hf : WeaklyConvex ρ f) :
    WeaklyConvex ρ (lipschitzMajorant f L) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let R := a * (lipschitzMajorant f L x + ρ / 2 * ‖x‖ ^ 2) +
    b * (lipschitzMajorant f L y + ρ / 2 * ‖y‖ ^ 2)
  have hsup : lipschitzMajorant f L z ≤ R - ρ / 2 * ‖z‖ ^ 2 := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨w, rfl⟩
    let v := w - z
    have ht := (weaklyConvex_translate_sub (c := L * ‖v‖) hf v).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hx := payoff_le_majorant hfinite x (x + v)
    have hy := payoff_le_majorant hfinite y (y + v)
    simp only [sourcePayoff, sub_add_cancel_left, norm_neg] at hx hy
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    have hw : z + v = w := by dsimp [v]; module
    have hnorm : ‖z - w‖ = ‖v‖ := by dsimp [v]; exact norm_sub_rev _ _
    change f (z + v) - L * ‖v‖ + ρ / 2 * ‖z‖ ^ 2 ≤
      a * (f (x + v) - L * ‖v‖ + ρ / 2 * ‖x‖ ^ 2) +
      b * (f (y + v) - L * ‖v‖ + ρ / 2 * ‖y‖ ^ 2) at ht
    rw [hw] at ht
    dsimp [R, sourcePayoff]
    rw [hnorm]
    linarith
  change lipschitzMajorant f L z + ρ / 2 * ‖z‖ ^ 2 ≤ R
  linarith

/-- Subcritical growth forces the defining supremum to be attained. -/
theorem majorant_source_exists [ProperSpace E] {f : E → ℝ} {L c A : ℝ} (u : E)
    (hc : 0 ≤ c) (hcL : c < L) (hf : Continuous f)
    (hgrowth : ∀ y, f y ≤ A + c * ‖u - y‖) (x : E) :
    ∃ y, sourcePayoff f L x y = lipschitzMajorant f L x := by
  have hfinite := majorant_finite_of_growth u hc hcL.le hgrowth
  let R : ℝ := (A + c * ‖u - x‖ - f x + 1) / (L - c)
  have hden : 0 < L - c := sub_pos.mpr hcL
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (by linarith [hgrowth x]) hden
  have hx : x ∈ Metric.closedBall x R := by simp [hR.le]
  have hcont : Continuous (sourcePayoff f L x) :=
    hf.sub (continuous_const.mul (continuous_const.sub continuous_id).norm)
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall x R).exists_isMaxOn
    ⟨x, hx⟩ hcont.continuousOn
  have hglobal : ∀ y, sourcePayoff f L x y ≤ sourcePayoff f L x p := by
    intro y
    by_cases hy : y ∈ Metric.closedBall x R
    · exact hmax hy
    · have hdist : R < ‖x - y‖ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev y x, not_le] using hy
      have hn : ‖u - y‖ ≤ ‖u - x‖ + ‖x - y‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (u - x) (x - y)
      have htri := mul_le_mul_of_nonneg_left hn hc
      have hfar := mul_lt_mul_of_pos_left hdist hden
      have hRid : (L - c) * R = A + c * ‖u - x‖ - f x + 1 := by
        dsimp [R]
        field_simp
      rw [hRid] at hfar
      have hxy : sourcePayoff f L x y ≤ sourcePayoff f L x x := by
        dsimp [sourcePayoff]
        simp only [sub_self, norm_zero, mul_zero, sub_zero]
        linarith [hgrowth y]
      exact hxy.trans (hmax hx)
  refine ⟨p, le_antisymm (payoff_le_majorant hfinite x p) ?_⟩
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨y, rfl⟩; exact hglobal y)

end WC
