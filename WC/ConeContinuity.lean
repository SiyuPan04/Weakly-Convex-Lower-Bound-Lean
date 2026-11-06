import WC.BoundaryLower
import WC.ModelMeasurability

/-! Joint continuity of the auxiliary cone and its own Moreau gradient,
including at the tip. Translation transports the genuine proximal point. -/

noncomputable section
namespace WC.BoundaryLower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normCone_proxObjective_translation (lam v : ℝ) (c x p : E) :
    proxObjective lam (normCone v c) x (c + p) =
      proxObjective lam (normCone v 0) (x - c) p := by
  simp only [proxObjective, normCone, sub_zero]
  rw [show c + p - c = p by module, show x - (c + p) = x - c - p by module]

theorem normCone_joint_continuous (v a : ℝ) :
    Continuous (fun p : E × E => normCone v (a • p.1) p.2) :=
  continuous_const.mul ((continuous_snd.sub (continuous_const.smul continuous_fst)).norm)

variable [CompleteSpace E] [ProperSpace E]

theorem normCone_proximalPoint_translation {v ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 < ρ)
    (c x : E) : proximalPoint ρ (normCone v c) x =
      c + proximalPoint ρ (normCone v 0) (x - c) := by
  have hp := proximalPoint_spec hρ hv (normCone_lipschitz hv c) x
  have hq := proximalPoint_spec hρ hv (normCone_lipschitz hv (0 : E)) (x - c)
  apply hp.unique hρ (normCone_weaklyConvex hv hρ.le c)
  intro y
  have hy := normCone_proxObjective_translation (1 / (2 * ρ)) v c x (y - c)
  rw [show c + (y - c) = y by module] at hy
  rw [normCone_proxObjective_translation, hy]
  exact hq (y - c)

theorem normCone_moreau_gradient_translation {v ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 < ρ)
    (c x : E) :
    gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v c)) x =
      gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v 0)) (x - c) := by
  rw [moreau_gradient_eq hρ hv (normCone_lipschitz hv c) (normCone_weaklyConvex hv hρ.le c),
    moreau_gradient_eq hρ hv (normCone_lipschitz hv (0 : E)) (normCone_weaklyConvex hv hρ.le (0 : E)),
    normCone_proximalPoint_translation hv hρ]
  congr 1
  module

theorem normCone_joint_moreau_gradient_continuous {v ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 < ρ) (a : ℝ) :
    Continuous (fun p : E × E =>
      gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v (a • p.1))) p.2) := by
  have hc := moreau_gradient_continuous hv hρ (normCone_lipschitz hv (0 : E))
    (normCone_weaklyConvex hv hρ.le (0 : E))
  have hshift : Continuous (fun p : E × E => p.2 - a • p.1) :=
    continuous_snd.sub (continuous_const.smul continuous_fst)
  have h := hc.comp hshift
  convert h using 1
  funext p
  exact normCone_moreau_gradient_translation hv hρ (a • p.1) p.2

theorem cone_family_joint_moreau_gradient_continuous {G ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G) :
    Continuous (fun p : E × E =>
      gradient (moreauEnvelope (1 / (2 * ρ))
        (normCone (coneVelocity G ε) (coneOffset ρ G ε • p.1))) p.2) :=
  normCone_joint_moreau_gradient_continuous
    (lt_trans hε (coneVelocity_bounds hε hεG).1).le hρ _

end WC.BoundaryLower
