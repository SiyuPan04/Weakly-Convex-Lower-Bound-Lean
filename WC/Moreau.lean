import WC.Proximal
import WC.Subgradient
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
The actual Moreau-envelope derivative. The envelope is the infimum defined in
`WC.Basic`; the proximal point is obtained by the compactness proof in
`WC.Proximal`. This is not a definition of an abstract stationarity oracle.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def proximalPoint (ρ : ℝ) (f : E → ℝ) (x : E) : E :=
  by
    classical
    exact if h : ∃ p, IsProxPoint (1 / (2 * ρ)) f x p then Classical.choose h else x

theorem proximalPoint_spec [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f) (x : E) :
    IsProxPoint (1 / (2 * ρ)) f x (proximalPoint ρ f x) := by
  have hex : ∃ p, IsProxPoint (1 / (2 * ρ)) f x p := by
    obtain ⟨p, hp⟩ := exists_quadraticMinimizer hρ hG hlip x
    refine ⟨p, fun y => ?_⟩
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hp y
  simp only [proximalPoint, dif_pos hex]
  exact Classical.choose_spec hex

theorem proximal_center_pairing {ρ : ℝ} {f : E → ℝ} {x y p q : E}
    (hρ : 0 < ρ) (hwc : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p)
    (hq : IsProxPoint (1 / (2 * ρ)) f y q) :
    ‖q - p‖ ^ 2 ≤ 2 * inner ℝ (y - x) (q - p) := by
  have hs₁ := hp.strong_minimum hρ hwc q
  have hs₂ := hq.strong_minimum hρ hwc p
  rw [norm_sub_rev p q] at hs₂
  simp only [proxObjective_eq_quadratic hρ.ne'] at hs₁ hs₂
  have halg : quadraticObjective ρ f x q + quadraticObjective ρ f y p -
      quadraticObjective ρ f x p - quadraticObjective ρ f y q =
      ρ * (2 * inner ℝ (y - x) (q - p)) := by
    simp only [quadraticObjective, norm_sub_sq_real, inner_sub_left, inner_sub_right]
    ring
  have hm : ρ * ‖q - p‖ ^ 2 ≤ ρ * (2 * inner ℝ (y - x) (q - p)) := by
    linarith
  exact (mul_le_mul_iff_right₀ hρ).mp hm

theorem proximal_displacement_lipschitz {ρ : ℝ} {f : E → ℝ} {x y p q : E}
    (hρ : 0 < ρ) (hwc : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p)
    (hq : IsProxPoint (1 / (2 * ρ)) f y q) :
    ‖q - p‖ ≤ 2 * ‖y - x‖ := by
  have hm := proximal_center_pairing hρ hwc hp hq
  have hi := real_inner_le_norm (y - x) (q - p)
  nlinarith [norm_nonneg (y - x), norm_nonneg (q - p)]

theorem envelope_expansion_upper {ρ : ℝ} {f : E → ℝ} {x y p q : E}
    (hρ : 0 < ρ)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p)
    (hq : IsProxPoint (1 / (2 * ρ)) f y q) :
    moreauEnvelope (1 / (2 * ρ)) f y - moreauEnvelope (1 / (2 * ρ)) f x -
      inner ℝ ((2 * ρ) • (x - p)) (y - x) ≤ ρ * ‖y - x‖ ^ 2 := by
  rw [hp.envelope_eq, hq.envelope_eq]
  have hmin := hq p
  simp only [proxObjective_eq_quadratic hρ.ne'] at hmin ⊢
  have hnorm : ‖y - p‖ ^ 2 = ‖x - p‖ ^ 2 +
      2 * inner ℝ (x - p) (y - x) + ‖y - x‖ ^ 2 := by
    have heq : (x - p) + (y - x) = y - p := by module
    simpa only [heq] using norm_add_sq_real (x - p) (y - x)
  simp only [quadraticObjective] at hmin ⊢
  rw [real_inner_smul_left]
  nlinarith [hnorm]

theorem envelope_expansion_bound {ρ : ℝ} {f : E → ℝ} {x y p q : E}
    (hρ : 0 < ρ) (hwc : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p)
    (hq : IsProxPoint (1 / (2 * ρ)) f y q) :
    |moreauEnvelope (1 / (2 * ρ)) f y - moreauEnvelope (1 / (2 * ρ)) f x -
      inner ℝ ((2 * ρ) • (x - p)) (y - x)| ≤ 5 * ρ * ‖y - x‖ ^ 2 := by
  apply abs_le.mpr
  have hu := envelope_expansion_upper hρ hp hq
  constructor
  · have hl := envelope_expansion_upper hρ hq hp
    rw [norm_sub_rev x y] at hl
    have hprox := proximal_displacement_lipschitz hρ hwc hp hq
    have hi := real_inner_le_norm (q - p) (y - x)
    have hid : inner ℝ ((2 * ρ) • (x - p)) (y - x) +
        inner ℝ ((2 * ρ) • (y - q)) (x - y) =
        2 * ρ * (inner ℝ (q - p) (y - x) - ‖y - x‖ ^ 2) := by
      simp only [real_inner_smul_left, inner_sub_left, inner_sub_right,
        norm_sub_sq_real, real_inner_self_eq_norm_sq]
      simp only [real_inner_comm]
      ring
    have hprod := mul_le_mul_of_nonneg_right hprox (norm_nonneg (y - x))
    have hiR := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * ρ by positivity)
    have hpR := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * ρ by positivity)
    nlinarith [hid, mul_nonneg hρ.le (sq_nonneg ‖y - x‖)]
  · nlinarith [mul_nonneg hρ.le (sq_nonneg ‖y - x‖)]

theorem moreau_hasGradientAt [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) :
    HasGradientAt (moreauEnvelope (1 / (2 * ρ)) f)
      ((2 * ρ) • (x - proximalPoint ρ f x)) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hbig :
      (fun h : E => moreauEnvelope (1 / (2 * ρ)) f (x + h) -
        moreauEnvelope (1 / (2 * ρ)) f x -
        inner ℝ ((2 * ρ) • (x - proximalPoint ρ f x)) h) =O[nhds 0]
        (fun h : E => ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (5 * ρ)
    apply Filter.Eventually.of_forall
    intro h
    have hb := envelope_expansion_bound hρ hwc
      (proximalPoint_spec hρ hG hlip x) (proximalPoint_spec hρ hG hlip (x + h))
    simpa only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)]
      using hb
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

/-- The standard gradient is proved equal to the proximal residual. -/
theorem moreau_gradient_eq [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) :
    gradient (moreauEnvelope (1 / (2 * ρ)) f) x =
      (2 * ρ) • (x - proximalPoint ρ f x) :=
  (moreau_hasGradientAt hρ hG hlip hwc x).gradient

theorem moreau_gradient_norm_le [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) x‖ ≤ G := by
  rw [moreau_gradient_eq hρ hG hlip hwc]
  exact ((proximalPoint_spec hρ hG hlip x).weakSubgradient hρ hwc).norm_le hρ.le hG hlip

end WC
