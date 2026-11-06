import WC.Scaling
import WC.Subgradient
import WC.Moreau
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul

/-!
# Isometric lifting

Appendix `app:isometry`: the transpose is the actual Hilbert-space adjoint
of a linear isometry. Orthogonal decomposition, regularity, and proximal
transport are proved from this operator, without a decomposition certificate.
-/

noncomputable section
namespace WC

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def isometryProjection (U : E →ₗᵢ[ℝ] F) : F →L[ℝ] E := U.toContinuousLinearMap.adjoint

def orthogonalPart (U : E →ₗᵢ[ℝ] F) (x : F) : F := x - U (isometryProjection U x)

def isometricLift (U : E →ₗᵢ[ℝ] F) (f : E → ℝ) (x : F) : ℝ :=
  f (isometryProjection U x)

@[simp] theorem isometryProjection_map (U : E →ₗᵢ[ℝ] F) (z : E) :
    isometryProjection U (U z) = z := by
  have h := congrArg (fun A : E →L[ℝ] E => A z) U.adjoint_comp_self
  change isometryProjection U (U z) = z at h
  exact h

@[simp] theorem isometryProjection_orthogonalPart (U : E →ₗᵢ[ℝ] F) (x : F) :
    isometryProjection U (orthogonalPart U x) = 0 := by
  simp [orthogonalPart]

theorem inner_map_orthogonalPart (U : E →ₗᵢ[ℝ] F) (z : E) (x : F) :
    inner ℝ (U z) (orthogonalPart U x) = 0 := by
  change inner ℝ (U.toContinuousLinearMap z) (orthogonalPart U x) = 0
  rw [← U.toContinuousLinearMap.adjoint_inner_right]
  change inner ℝ z (isometryProjection U (orthogonalPart U x)) = 0
  simp

theorem norm_decomposition (U : E →ₗᵢ[ℝ] F) (x : F) :
    ‖x‖ ^ 2 = ‖isometryProjection U x‖ ^ 2 + ‖orthogonalPart U x‖ ^ 2 := by
  have h := norm_add_sq_real (U (isometryProjection U x)) (orthogonalPart U x)
  rw [inner_map_orthogonalPart, U.norm_map] at h
  simpa [orthogonalPart] using h

theorem isometryProjection_norm_le (U : E →ₗᵢ[ℝ] F) (x : F) :
    ‖isometryProjection U x‖ ≤ ‖x‖ := by
  have h := norm_decomposition U x
  nlinarith [norm_nonneg (isometryProjection U x), norm_nonneg x,
    sq_nonneg ‖orthogonalPart U x‖]

theorem isometryProjection_surjective (U : E →ₗᵢ[ℝ] F) :
    Function.Surjective (isometryProjection U) := fun z => ⟨U z, isometryProjection_map U z⟩

theorem isometricLift_gap {Δ : ℝ} {f : E → ℝ} (U : E →ₗᵢ[ℝ] F)
    (hf : GapBound Δ f) : GapBound Δ (isometricLift U f) := by
  intro x
  simpa [isometricLift] using hf (isometryProjection U x)

theorem isometricLift_range (U : E →ₗᵢ[ℝ] F) (f : E → ℝ) :
    Set.range (isometricLift U f) = Set.range f := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨isometryProjection U x, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨U z, by simp [isometricLift]⟩

theorem isometricLift_lipschitz {G : ℝ} {f : E → ℝ} (U : E →ₗᵢ[ℝ] F)
    (hG : 0 ≤ G) (hf : GloballyLipschitz G f) :
    GloballyLipschitz G (isometricLift U f) := by
  intro x y
  have h := hf (isometryProjection U x) (isometryProjection U y)
  have hc := mul_le_mul_of_nonneg_left (isometryProjection_norm_le U (x - y)) hG
  rw [map_sub] at hc
  exact h.trans hc

theorem isometricLift_weaklyConvex {ρ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) :
    WeaklyConvex ρ (isometricLift U f) := by
  let P := isometryProjection U
  let Q : F →ₗ[ℝ] F := LinearMap.id - U.toLinearMap.comp P.toLinearMap
  have hbase : ConvexOn ℝ Set.univ (fun x => f (P x) + ρ / 2 * ‖P x‖ ^ 2) := by
    simpa [Function.comp_def] using hf.comp_linearMap P.toLinearMap
  have hnorm : ConvexOn ℝ Set.univ (fun x : F => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have horth : ConvexOn ℝ Set.univ (fun x : F => ρ / 2 * ‖Q x‖ ^ 2) := by
    simpa using (hnorm.comp_linearMap Q).smul (show 0 ≤ ρ / 2 by positivity)
  have hadd := hbase.add horth
  apply hadd.congr
  intro x _
  have hdecomp := norm_decomposition U x
  change f (P x) + ρ / 2 * ‖P x‖ ^ 2 + ρ / 2 * ‖Q x‖ ^ 2 =
    isometricLift U f x + ρ / 2 * ‖x‖ ^ 2
  change f (isometryProjection U x) + ρ / 2 * ‖isometryProjection U x‖ ^ 2 +
    ρ / 2 * ‖orthogonalPart U x‖ ^ 2 =
    f (isometryProjection U x) + ρ / 2 * ‖x‖ ^ 2
  rw [hdecomp]
  ring

theorem isometricLift_admissible {G ρ Δ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hf : Admissible G ρ Δ f) : Admissible G ρ Δ (isometricLift U f) :=
  ⟨isometricLift_weaklyConvex U hρ hf.weaklyConvex,
    isometricLift_lipschitz U hG hf.lipschitz, isometricLift_gap U hf.gap⟩

/-- Lift a proximal point while retaining the orthogonal component of its center. -/
def proxLiftPoint (U : E →ₗᵢ[ℝ] F) (x : F) (p : E) : F :=
  U p + orthogonalPart U x

@[simp] theorem isometryProjection_proxLiftPoint (U : E →ₗᵢ[ℝ] F) (x : F) (p : E) :
    isometryProjection U (proxLiftPoint U x p) = p := by
  simp [proxLiftPoint]

theorem sub_proxLiftPoint (U : E →ₗᵢ[ℝ] F) (x : F) (p : E) :
    x - proxLiftPoint U x p = U (isometryProjection U x - p) := by
  simp only [proxLiftPoint, orthogonalPart, map_sub]
  module

theorem proxObjective_isometricLift_point (U : E →ₗᵢ[ℝ] F)
    (lam : ℝ) (f : E → ℝ) (x : F) (p : E) :
    proxObjective lam (isometricLift U f) x (proxLiftPoint U x p) =
      proxObjective lam f (isometryProjection U x) p := by
  simp only [proxObjective, isometricLift, isometryProjection_proxLiftPoint,
    sub_proxLiftPoint, U.norm_map]

/-- Genuine global minimizers transport by the formula in the appendix. -/
theorem IsProxPoint.isometricLift {lam : ℝ} {f : E → ℝ} {x : F} {p : E}
    (U : E →ₗᵢ[ℝ] F) (hlam : 0 < lam)
    (hp : IsProxPoint lam f (isometryProjection U x) p) :
    IsProxPoint lam (isometricLift U f) x (proxLiftPoint U x p) := by
  intro y
  rw [proxObjective_isometricLift_point]
  apply (hp (isometryProjection U y)).trans
  change f (isometryProjection U y) +
      ‖isometryProjection U x - isometryProjection U y‖ ^ 2 / (2 * lam) ≤
    f (isometryProjection U y) + ‖x - y‖ ^ 2 / (2 * lam)
  have hc := isometryProjection_norm_le U (x - y)
  rw [map_sub] at hc
  have hsq : ‖isometryProjection U x - isometryProjection U y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [norm_nonneg (isometryProjection U x - isometryProjection U y), norm_nonneg (x - y)]
  exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hsq
    (show 0 ≤ 2 * lam by positivity))

theorem proxLiftPoint_minimizer_iff {lam : ℝ} {f : E → ℝ} {x : F} {p : E}
    (U : E →ₗᵢ[ℝ] F) (hlam : 0 < lam) :
    IsProxPoint lam (isometricLift U f) x (proxLiftPoint U x p) ↔
      IsProxPoint lam f (isometryProjection U x) p := by
  constructor
  · intro hp z
    have h := hp (proxLiftPoint U x z)
    simpa only [proxObjective_isometricLift_point] using h
  · exact IsProxPoint.isometricLift U hlam

/-- The Moreau-envelope values agree whenever a proximal minimizer exists. -/
theorem moreauEnvelope_isometricLift {lam : ℝ} {f : E → ℝ} {x : F} {p : E}
    (U : E →ₗᵢ[ℝ] F) (hlam : 0 < lam)
    (hp : IsProxPoint lam f (isometryProjection U x) p) :
    moreauEnvelope lam (isometricLift U f) x = moreauEnvelope lam f (isometryProjection U x) := by
  rw [(hp.isometricLift U hlam).envelope_eq, hp.envelope_eq,
    proxObjective_isometricLift_point]

/-- Exact vector residual transport, independently of differentiability theory. -/
theorem proxResidual_isometricLift (U : E →ₗᵢ[ℝ] F)
    (lam : ℝ) (x : F) (p : E) :
    proxResidual lam x (proxLiftPoint U x p) =
      U (proxResidual lam (isometryProjection U x) p) := by
  simp [proxResidual, sub_proxLiftPoint]

theorem proxResidual_isometricLift_norm (U : E →ₗᵢ[ℝ] F)
    (lam : ℝ) (x : F) (p : E) :
    ‖proxResidual lam x (proxLiftPoint U x p)‖ =
      ‖proxResidual lam (isometryProjection U x) p‖ := by
  rw [proxResidual_isometricLift, U.norm_map]

theorem inner_self_orthogonalPart (U : E →ₗᵢ[ℝ] F) (v : F) :
    inner ℝ v (orthogonalPart U v) = ‖orthogonalPart U v‖ ^ 2 := by
  calc
    inner ℝ v (orthogonalPart U v) =
        inner ℝ (U (isometryProjection U v) + orthogonalPart U v) (orthogonalPart U v) := by
      congr 1
      simp [orthogonalPart]
    _ = ‖orthogonalPart U v‖ ^ 2 := by
      rw [inner_add_left, inner_map_orthogonalPart, real_inner_self_eq_norm_sq, zero_add]

/-- A lifted function has no subgradient component perpendicular to the frame. -/
theorem WeakSubgradient.isometricLift_range {ρ : ℝ} {f : E → ℝ} {x v : F}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 ≤ ρ)
    (h : WeakSubgradient ρ (isometricLift U f) x v) :
    v = U (isometryProjection U v) := by
  let t : ℝ := 1 / (ρ + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hteq : t * (ρ + 1) = 1 := by dsimp [t]; field_simp
  have hteqmul := congrArg (fun s : ℝ => s * t) hteq
  have hcoef : 0 < t - ρ / 2 * t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs := h (x + t • orthogonalPart U v)
  change f (isometryProjection U x) +
      inner ℝ v ((x + t • orthogonalPart U v) - x) -
      ρ / 2 * ‖(x + t • orthogonalPart U v) - x‖ ^ 2 ≤
    f (isometryProjection U (x + t • orthogonalPart U v)) at hs
  simp only [map_add, map_smul, isometryProjection_orthogonalPart, smul_zero,
    add_zero, add_sub_cancel_left, real_inner_smul_right, inner_self_orthogonalPart,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hs
  have hs' : (t - ρ / 2 * t ^ 2) * ‖orthogonalPart U v‖ ^ 2 ≤ 0 := by nlinarith [hs]
  have hsq : ‖orthogonalPart U v‖ ^ 2 ≤ 0 := by
    by_contra hh
    have := mul_pos hcoef (lt_of_not_ge hh)
    linarith
  have hzero : ‖orthogonalPart U v‖ = 0 := by nlinarith [norm_nonneg (orthogonalPart U v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Exact transport of the complete weak subdifferential. -/
theorem weakSubgradient_isometricLift_iff {ρ : ℝ} {f : E → ℝ} {x v : F}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 ≤ ρ) :
    WeakSubgradient ρ (isometricLift U f) x v ↔
      ∃ w : E, WeakSubgradient ρ f (isometryProjection U x) w ∧ v = U w := by
  constructor
  · intro h
    have hvrange := h.isometricLift_range U hρ
    refine ⟨isometryProjection U v, ?_, hvrange⟩
    intro z
    have hs := h (x + U (z - isometryProjection U x))
    rw [hvrange] at hs
    have hquery : isometryProjection U (x + U (z - isometryProjection U x)) = z := by simp
    change f (isometryProjection U x) +
      inner ℝ (U (isometryProjection U v)) ((x + U (z - isometryProjection U x)) - x) -
      ρ / 2 * ‖(x + U (z - isometryProjection U x)) - x‖ ^ 2 ≤
      f (isometryProjection U (x + U (z - isometryProjection U x))) at hs
    rw [add_sub_cancel_left, U.inner_map_map, U.norm_map, hquery] at hs
    exact hs
  · rintro ⟨w, hw, rfl⟩ y
    have hs := hw (isometryProjection U y)
    have hinter : inner ℝ (U w) (y - x) =
        inner ℝ w (isometryProjection U y - isometryProjection U x) := by
      have h := U.toContinuousLinearMap.adjoint_inner_right w (y - x)
      simpa [isometryProjection, map_sub] using h.symm
    have hc := isometryProjection_norm_le U (y - x)
    rw [map_sub] at hc
    have hsq : ‖isometryProjection U y - isometryProjection U x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
      nlinarith [norm_nonneg (isometryProjection U y - isometryProjection U x), norm_nonneg (y - x)]
    change f (isometryProjection U x) + inner ℝ (U w) (y - x) -
        ρ / 2 * ‖y - x‖ ^ 2 ≤ f (isometryProjection U y)
    rw [hinter]
    have hmult := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ρ / 2 by positivity)
    linarith

/-- Appendix (i), for the actual Fréchet subdifferential of a weakly convex function. -/
theorem frechetSubdifferential_isometricLift {ρ : ℝ} {f : E → ℝ} (x : F)
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) :
    {v : F | FrechetSubgradient (isometricLift U f) x v} =
      U '' {w : E | FrechetSubgradient f (isometryProjection U x) w} := by
  ext v
  change FrechetSubgradient (isometricLift U f) x v ↔
    ∃ w, FrechetSubgradient f (isometryProjection U x) w ∧ U w = v
  rw [← weakSubgradient_iff_frechet hρ (isometricLift_weaklyConvex U hρ hf),
    weakSubgradient_isometricLift_iff U hρ]
  constructor
  · rintro ⟨w, hw, hv⟩
    exact ⟨w, (weakSubgradient_iff_frechet hρ hf).1 hw, hv.symm⟩
  · rintro ⟨w, hw, hv⟩
    exact ⟨w, (weakSubgradient_iff_frechet hρ hf).2 hw, hv.symm⟩

/-- The chosen genuine proximal point satisfies the exact lifting formula. -/
theorem proximalPoint_isometricLift [ProperSpace E] [ProperSpace F]
    {G ρ : ℝ} {f : E → ℝ} (U : E →ₗᵢ[ℝ] F)
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : F) :
    proximalPoint ρ (isometricLift U f) x =
      proxLiftPoint U x (proximalPoint ρ f (isometryProjection U x)) := by
  have hleft := proximalPoint_spec hρ hG (isometricLift_lipschitz U hG hlip) x
  have hright := (proximalPoint_spec hρ hG hlip (isometryProjection U x)).isometricLift U
    (show 0 < 1 / (2 * ρ) by positivity)
  apply quadraticMinimizer_unique hρ (isometricLift_weaklyConvex U hρ.le hwc)
  · intro y
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hleft y
  · intro y
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hright y

/-- Appendix (ii), now for the actual analytic gradient of the Moreau envelope. -/
theorem moreau_gradient_isometricLift [ProperSpace E] [ProperSpace F]
    {G ρ : ℝ} {f : E → ℝ} (U : E →ₗᵢ[ℝ] F)
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : F) :
    gradient (moreauEnvelope (1 / (2 * ρ)) (isometricLift U f)) x =
      U (gradient (moreauEnvelope (1 / (2 * ρ)) f) (isometryProjection U x)) := by
  rw [moreau_gradient_eq hρ hG (isometricLift_lipschitz U hG hlip)
    (isometricLift_weaklyConvex U hρ.le hwc),
    proximalPoint_isometricLift U hG hρ hlip hwc,
    sub_proxLiftPoint, moreau_gradient_eq hρ hG hlip hwc, map_smul]

theorem moreau_gradient_isometricLift_norm [ProperSpace E] [ProperSpace F]
    {G ρ : ℝ} {f : E → ℝ} (U : E →ₗᵢ[ℝ] F)
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : F) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) (isometricLift U f)) x‖ =
      ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) (isometryProjection U x)‖ := by
  rw [moreau_gradient_isometricLift U hG hρ hlip hwc, U.norm_map]

end WC
