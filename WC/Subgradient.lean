import WC.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Actual subgradients of weakly convex functions

The definitions below are supporting inequalities for actual functions.
`FrechetSubgradient` is the usual epsilon-delta first-order lower support
condition. It is not an opaque oracle field. No finite-dimensionality
assumption is needed for the elementary results proved here.
-/

noncomputable section

namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A global supporting linear functional, represented by its inner-product vector. -/
def ConvexSubgradient (f : E → ℝ) (x v : E) : Prop :=
  ∀ y, f x + inner ℝ v (y - x) ≤ f y

/-- A global quadratic supporting inequality with weak-convexity modulus `ρ`. -/
def WeakSubgradient (ρ : ℝ) (f : E → ℝ) (x v : E) : Prop :=
  ∀ y, f x + inner ℝ v (y - x) - ρ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- The Fréchet subgradient condition, expressed without a punctured
neighborhood: at `y = x` the inequality holds with equality. -/
def FrechetSubgradient (f : E → ℝ) (x v : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ →
    f x + inner ℝ v (y - x) - ε * ‖y - x‖ ≤ f y

/-- Expand the convexifying quadratic around the supporting point. -/
theorem weakSubgradient_iff_convexification {ρ : ℝ} {f : E → ℝ} {x v : E} :
    WeakSubgradient ρ f x v ↔
      ConvexSubgradient (fun y => f y + ρ / 2 * ‖y‖ ^ 2) x (v + ρ • x) := by
  have norm_identity (y : E) :
      ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
    simpa using norm_add_sq_real x (y - x)
  constructor
  · intro h y
    have hy := h y
    dsimp
    simp only [inner_add_left, real_inner_smul_left]
    rw [norm_identity y]
    nlinarith [hy]
  · intro h y
    have hy := h y
    dsimp at hy
    simp only [inner_add_left, real_inner_smul_left] at hy
    rw [norm_identity y] at hy
    nlinarith [hy]

/-- A quadratic support is a genuine Fréchet support. -/
theorem WeakSubgradient.frechet {ρ : ℝ} {f : E → ℝ} {x v : E}
    (hρ : 0 ≤ ρ) (h : WeakSubgradient ρ f x v) : FrechetSubgradient f x v := by
  intro ε hε
  let δ := ε / (ρ + 1)
  have hden : 0 < ρ + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hnorm := norm_nonneg (y - x)
  have hy' : ‖y - x‖ * (ρ + 1) < ε := (lt_div_iff₀ hden).mp hy
  have hsmall : ρ / 2 * ‖y - x‖ ^ 2 ≤ ε * ‖y - x‖ := by
    nlinarith [mul_nonneg hρ hnorm,
      mul_nonneg hnorm (le_of_lt (sub_pos.mpr hy'))]
  have := h y
  linarith

/-- A Fréchet support to a convex function supports it globally. The
proof uses convexity on arbitrarily short initial portions of a segment. -/
theorem ConvexOn.support_of_frechet {f : E → ℝ} {x v : E}
    (hf : ConvexOn ℝ Set.univ f) (h : FrechetSubgradient f x v) :
    ConvexSubgradient f x v := by
  intro y
  by_contra hfail
  have hgap : 0 < f x + inner ℝ v (y - x) - f y := by linarith
  have hd : 0 < ‖y - x‖ := by
    by_contra hn
    have heq : y = x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _)))
    subst y
    simp at hgap
  let ε := (f x + inner ℝ v (y - x) - f y) / (2 * ‖y - x‖)
  have hε : 0 < ε := div_pos hgap (by positivity)
  obtain ⟨δ, hδ, hlocal⟩ := h ε hε
  let t := min (δ / (2 * ‖y - x‖)) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (div_pos hδ (by positivity)) (by norm_num)
  have ht_half : t ≤ 1 / 2 := min_le_right _ _
  have htδ : t * (2 * ‖y - x‖) ≤ δ :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hdist : ‖(x + t • (y - x)) - x‖ < δ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hlocal' := hlocal (x + t • (y - x)) hdist
  simp only [add_sub_cancel_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht] at hlocal'
  have hconv := hf.2 (Set.mem_univ x) (Set.mem_univ y)
    (show 0 ≤ 1 - t by linarith) (le_of_lt ht) (show 1 - t + t = 1 by ring)
  have hpoint : (1 - t) • x + t • y = x + t • (y - x) := by module
  rw [hpoint] at hconv
  simp only [smul_eq_mul] at hconv
  have heps : ε * (2 * ‖y - x‖) = f x + inner ℝ v (y - x) - f y :=
    div_mul_cancel₀ _ (by positivity)
  have hdivided : f x + inner ℝ v (y - x) - f y ≤ ε * ‖y - x‖ := by
    nlinarith [hconv, hlocal']
  nlinarith

/-- For a weakly convex function, the global quadratic support and the
Fréchet subgradient condition agree. -/
theorem weakSubgradient_iff_frechet {ρ : ℝ} {f : E → ℝ} {x v : E}
    (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) :
    WeakSubgradient ρ f x v ↔ FrechetSubgradient f x v := by
  constructor
  · exact WeakSubgradient.frechet hρ
  · intro h
    apply weakSubgradient_iff_convexification.mpr
    apply ConvexOn.support_of_frechet hf
    intro ε hε
    obtain ⟨δ, hδ, hlocal⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have hsupport := hlocal y hy
    have hnorm :
        ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
      simpa using norm_add_sq_real x (y - x)
    simp only [inner_add_left, real_inner_smul_left]
    rw [hnorm]
    nlinarith [mul_nonneg hρ (sq_nonneg ‖y - x‖)]

/-- Every Fréchet subgradient of a globally Lipschitz function has norm
bounded by the Lipschitz constant. Nonnegativity of `G` covers the zero space. -/
theorem FrechetSubgradient.norm_le {G : ℝ} {f : E → ℝ} {x v : E}
    (hG : 0 ≤ G) (hf : GloballyLipschitz G f) (h : FrechetSubgradient f x v) :
    ‖v‖ ≤ G := by
  by_contra hfail
  have hvG : G < ‖v‖ := lt_of_not_ge hfail
  have hv : 0 < ‖v‖ := lt_of_le_of_lt hG hvG
  let ε := (‖v‖ - G) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hlocal⟩ := h ε hε
  let t := δ / (2 * ‖v‖)
  have ht : 0 < t := div_pos hδ (by positivity)
  have htd : t * (2 * ‖v‖) = δ := div_mul_cancel₀ _ (by positivity)
  have hdist : ‖(x + t • v) - x‖ < δ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hs := hlocal (x + t • v) hdist
  have hlip := (le_abs_self (f (x + t • v) - f x)).trans (hf (x + t • v) x)
  simp only [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hs hlip
  have hcancel : t * ‖v‖ * ‖v‖ ≤ t * ‖v‖ * (G + ε) := by nlinarith [hs, hlip]
  have hn := (mul_le_mul_iff_right₀ (mul_pos ht hv)).mp hcancel
  dsimp [ε] at hn
  linarith

theorem WeakSubgradient.norm_le {ρ G : ℝ} {f : E → ℝ} {x v : E}
    (hρ : 0 ≤ ρ) (hG : 0 ≤ G) (hf : GloballyLipschitz G f)
    (h : WeakSubgradient ρ f x v) : ‖v‖ ≤ G :=
  (h.frechet hρ).norm_le hG hf

/-- Exact expansion of the squared proximal penalty around `p`. -/
theorem proxPenalty_expansion (x p y : E) :
    ‖x - y‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
  have heq : x - y = (x - p) - (y - p) := by module
  rw [heq, norm_sub_sq_real]

/-- A quadratic support for the proximal residual gives the actual
strong-minimum inequality for the proximal objective. -/
theorem WeakSubgradient.proximal_support {ρ : ℝ} {f : E → ℝ} {x p : E}
    (h : WeakSubgradient ρ f p ((2 * ρ) • (x - p))) (y : E) :
    f p + ρ * ‖x - p‖ ^ 2 + ρ / 2 * ‖y - p‖ ^ 2 ≤ f y + ρ * ‖x - y‖ ^ 2 := by
  have hs := h y
  simp only [real_inner_smul_left] at hs
  rw [proxPenalty_expansion x p y]
  nlinarith [hs]

omit [InnerProductSpace ℝ E] in
/-- The manuscript's envelope parameter produces penalty `ρ ‖x-y‖²`. -/
theorem proxObjective_half_inv {ρ : ℝ} (f : E → ℝ) (x y : E) :
    proxObjective (1 / (2 * ρ)) f x y = f y + ρ * ‖x - y‖ ^ 2 := by
  dsimp [proxObjective]
  field_simp

/-- Genuine proximal optimality implies the weak-subgradient inclusion.
Minimality first gives a support with modulus `2ρ`; convexity of the
`ρ`-convexification sharpens its Fréchet support to modulus `ρ`. -/
theorem IsProxPoint.weakSubgradient {ρ : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p) :
    WeakSubgradient ρ f p ((2 * ρ) • (x - p)) := by
  apply (weakSubgradient_iff_frechet (le_of_lt hρ) hf).mpr
  apply WeakSubgradient.frechet (show 0 ≤ 2 * ρ by positivity)
    (ρ := 2 * ρ)
  intro y
  have hmin := hp y
  rw [proxObjective_half_inv, proxObjective_half_inv,
    proxPenalty_expansion x p y] at hmin
  simp only [real_inner_smul_left]
  nlinarith [hmin]

/-- A weak-subgradient inclusion proves global proximal minimality. -/
theorem WeakSubgradient.isProxPoint {ρ : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (h : WeakSubgradient ρ f p ((2 * ρ) • (x - p))) :
    IsProxPoint (1 / (2 * ρ)) f x p := by
  intro y
  rw [proxObjective_half_inv, proxObjective_half_inv]
  have hs := h.proximal_support y
  nlinarith [mul_nonneg (le_of_lt hρ) (sq_nonneg ‖y - p‖)]

theorem isProxPoint_iff_weakSubgradient {ρ : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) :
    IsProxPoint (1 / (2 * ρ)) f x p ↔
      WeakSubgradient ρ f p ((2 * ρ) • (x - p)) :=
  ⟨IsProxPoint.weakSubgradient hρ hf, WeakSubgradient.isProxPoint hρ⟩

/-- The strong-minimum estimate follows from actual proximal minimality. -/
theorem IsProxPoint.strong_minimum {ρ : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p) (y : E) :
    proxObjective (1 / (2 * ρ)) f x p + ρ / 2 * ‖y - p‖ ^ 2 ≤
      proxObjective (1 / (2 * ρ)) f x y := by
  rw [proxObjective_half_inv, proxObjective_half_inv]
  exact (hp.weakSubgradient hρ hf).proximal_support y

/-- Lipschitz functions have bounded actual proximal displacement. -/
theorem IsProxPoint.displacement_le {ρ G : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hf : WeaklyConvex ρ f)
    (hLip : GloballyLipschitz G f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p) :
    ‖x - p‖ ≤ G / (2 * ρ) := by
  have hn := (hp.weakSubgradient hρ hf).norm_le (le_of_lt hρ) hG hLip
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity)] at hn
  exact (le_div_iff₀ (show 0 < 2 * ρ by positivity)).mpr (by nlinarith [hn])

/-- A weakly convex proximal objective has at most one minimizer. -/
theorem IsProxPoint.unique {ρ : ℝ} {f : E → ℝ} {x p q : E}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f)
    (hp : IsProxPoint (1 / (2 * ρ)) f x p)
    (hq : IsProxPoint (1 / (2 * ρ)) f x q) : p = q := by
  have hs := hp.strong_minimum hρ hf q
  have hm := hq p
  have hzero : ‖q - p‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖q - p‖]
  have hnorm : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

end WC

