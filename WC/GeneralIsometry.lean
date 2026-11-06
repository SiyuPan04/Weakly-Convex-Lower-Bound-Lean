import WC.FiniteWeakConvex
import WC.Isometry

/-! The unrestricted finite-dimensional isometric Moreau identities from
the appendix, including weakly convex functions without a global
Lipschitz bound. -/

noncomputable section
namespace WC

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem finite_proximalPoint_isometricLift {ρ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : F) :
    proximalPoint ρ (isometricLift U f) x =
      proxLiftPoint U x (proximalPoint ρ f (isometryProjection U x)) := by
  have hleft := finite_proximalPoint_spec hρ (isometricLift_weaklyConvex U hρ.le hf) x
  have hright := (finite_proximalPoint_spec hρ hf (isometryProjection U x)).isometricLift U
    (show 0 < 1 / (2 * ρ) by positivity)
  apply quadraticMinimizer_unique hρ (isometricLift_weaklyConvex U hρ.le hf)
  · intro y
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hleft y
  · intro y
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hright y

omit [FiniteDimensional ℝ F] in
theorem finite_moreauEnvelope_isometricLift {ρ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : F) :
    moreauEnvelope (1 / (2 * ρ)) (isometricLift U f) x =
      moreauEnvelope (1 / (2 * ρ)) f (isometryProjection U x) :=
  moreauEnvelope_isometricLift U (by positivity)
    (finite_proximalPoint_spec hρ hf (isometryProjection U x))

theorem finite_moreau_gradient_isometricLift {ρ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : F) :
    gradient (moreauEnvelope (1 / (2 * ρ)) (isometricLift U f)) x =
      U (gradient (moreauEnvelope (1 / (2 * ρ)) f) (isometryProjection U x)) := by
  rw [finite_moreau_gradient_eq hρ (isometricLift_weaklyConvex U hρ.le hf),
    finite_proximalPoint_isometricLift U hρ hf, sub_proxLiftPoint,
    finite_moreau_gradient_eq hρ hf, map_smul]

theorem finite_moreau_gradient_isometricLift_norm {ρ : ℝ} {f : E → ℝ}
    (U : E →ₗᵢ[ℝ] F) (hρ : 0 < ρ) (hf : WeaklyConvex ρ f) (x : F) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) (isometricLift U f)) x‖ =
      ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) (isometryProjection U x)‖ := by
  rw [finite_moreau_gradient_isometricLift U hρ hf, U.norm_map]

end WC
