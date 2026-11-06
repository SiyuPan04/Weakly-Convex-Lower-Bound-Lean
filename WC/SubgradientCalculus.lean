import WC.Subgradient
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Contact and smooth-function rules for the actual Fréchet subdifferential. -/

noncomputable section
namespace WC

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem WeakSubgradient.contact {ρ : ℝ} {f g : E → ℝ} {x v : E}
    (h : WeakSubgradient ρ f x v) (hfg : ∀ y, f y ≤ g y) (hx : f x = g x) :
    WeakSubgradient ρ g x v := by
  intro y
  rw [← hx]
  exact (h y).trans (hfg y)

theorem FrechetSubgradient.contact {f g : E → ℝ} {x v : E}
    (h : FrechetSubgradient f x v) (hfg : ∀ y, f y ≤ g y) (hx : f x = g x) :
    FrechetSubgradient g x v := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [← hx]
  exact (hb y hy).trans (hfg y)

variable [CompleteSpace E]

theorem FrechetSubgradient.congr_eventuallyEq {f g : E → ℝ} {x v : E}
    (hv : FrechetSubgradient f x v) (heq : f =ᶠ[𝓝 x] g) : FrechetSubgradient g x v := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hb⟩ := hv ε hε
  obtain ⟨δ₂, hδ₂, he⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy => ?_⟩
  have hxy : f x = g x := heq.eq_of_nhds
  have hyy : f y = g y := he (by simpa only [dist_eq_norm] using hy.trans_le (min_le_right _ _))
  have hs := hb y (hy.trans_le (min_le_left _ _))
  rwa [hxy, hyy] at hs

theorem frechetSubgradient_congr_eventuallyEq {f g : E → ℝ} {x v : E}
    (heq : f =ᶠ[𝓝 x] g) : FrechetSubgradient f x v ↔ FrechetSubgradient g x v :=
  ⟨fun h => h.congr_eventuallyEq heq, fun h => h.congr_eventuallyEq heq.symm⟩

theorem HasGradientAt.frechetSubgradient {f : E → ℝ} {x w : E}
    (h : HasGradientAt f w x) : FrechetSubgradient f x w := by
  intro ε hε
  have hev := (hasGradientAt_iff_isLittleO.mp h).bound hε
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hyb := hb (show dist y x < δ by simpa only [dist_eq_norm] using hy)
  simp only [Real.norm_eq_abs] at hyb
  have hl := (abs_le.mp hyb).1
  linarith

theorem FrechetSubgradient.eq_gradient {f : E → ℝ} {x v w : E}
    (hv : FrechetSubgradient f x v) (hw : HasGradientAt f w x) : v = w := by
  by_contra hne
  let d := v - w
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let ε := ‖d‖ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ₁, hδ₁, hsub⟩ := hv ε hε
  have hev := (hasGradientAt_iff_isLittleO.mp hw).bound hε
  obtain ⟨δ₂, hδ₂, hder⟩ := Metric.eventually_nhds_iff.mp hev
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  let t := δ / (2 * ‖d‖)
  have ht : 0 < t := div_pos hδ (by positivity)
  have htn : t * ‖d‖ = δ / 2 := by dsimp [t]; field_simp
  have hnorm : ‖(x + t • d) - x‖ = δ / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htn]
  have hsmall₁ : ‖(x + t • d) - x‖ < δ₁ := by
    rw [hnorm]
    have := min_le_left δ₁ δ₂
    change δ ≤ δ₁ at this
    linarith
  have hsmall₂ : dist (x + t • d) x < δ₂ := by
    rw [dist_eq_norm, hnorm]
    have := min_le_right δ₁ δ₂
    change δ ≤ δ₂ at this
    linarith
  have hs := hsub (x + t • d) hsmall₁
  have he := hder hsmall₂
  simp only [Real.norm_eq_abs] at he
  have heup := (abs_le.mp he).2
  have hid : inner ℝ v ((x + t • d) - x) - inner ℝ w ((x + t • d) - x) = t * ‖d‖ ^ 2 := by
    rw [← inner_sub_left, add_sub_cancel_left, real_inner_smul_right]
    change t * inner ℝ d d = t * ‖d‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  have hbound : t * ‖d‖ ^ 2 ≤ t * (2 * ε * ‖d‖) := by
    rw [← htn] at hnorm
    nlinarith [hs, heup]
  have hcancel := (mul_le_mul_iff_right₀ ht).mp hbound
  dsimp [ε] at hcancel
  nlinarith [sq_pos_of_pos hd]

theorem frechetSubgradient_iff_gradient {f : E → ℝ} {x v w : E}
    (hw : HasGradientAt f w x) : FrechetSubgradient f x v ↔ v = w := by
  constructor
  · exact fun hv => hv.eq_gradient hw
  · intro h
    subst v
    exact HasGradientAt.frechetSubgradient hw

theorem hasGradientAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E => ‖y‖) (‖x‖⁻¹ • x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hnorm)
  have heq : (InnerProductSpace.toDual ℝ E) (‖x‖⁻¹ • x) =
      (1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 : ℕ) • innerSL ℝ x := by
    ext y
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, innerSL_apply_apply,
      Real.sqrt_sq (norm_nonneg x), nsmul_eq_mul, smul_eq_mul]
    field_simp <;> norm_num
  rw [heq]
  simpa only [Real.sqrt_sq (norm_nonneg _)] using h

theorem hasGradientAt_distance_penalty {L : ℝ} {x y : E} (hxy : x ≠ y) :
    HasGradientAt (fun z : E => L * ‖x - z‖)
      ((-L / ‖x - y‖) • (x - y)) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hn := (hasGradientAt_norm_of_ne_zero (sub_ne_zero.mpr hxy)).hasFDerivAt
  have hd := (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
  have hc := (hn.comp y hd).const_mul L
  convert! hc using 1
  ext z
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
    ContinuousLinearMap.comp_apply, sub_apply, zero_apply, ContinuousLinearMap.id_apply,
    zero_sub, neg_apply, real_inner_smul_left, inner_neg_right, smul_eq_mul]
  ring

end WC
