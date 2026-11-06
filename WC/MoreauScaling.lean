import WC.Moreau

/-! The gradient identity in equation `newrand:actual-scaling`, for the actual
Moreau-envelope gradient rather than a defined residual. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem physical_moreau_gradient {G ρ Δ : ℝ} {f : E → ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hf : Admissible 1 1 Δ f) (x : E) :
    gradient (moreauEnvelope (1 / (2 * ρ))
        (scaleFunction (G ^ 2 / ρ) (ρ / G) f)) x =
      G • gradient (moreauEnvelope (1 / 2) f) ((ρ / G) • x) := by
  let F := scaleFunction (G ^ 2 / ρ) (ρ / G) f
  have hF : Admissible G ρ ((G ^ 2 / ρ) * Δ) F := physical_admissible_scale hG hρ hf
  let p := proximalPoint ρ F x
  have hp : IsProxPoint (1 / (2 * ρ)) F x p :=
    proximalPoint_spec hρ hG.le hF.lipschitz x
  have ht := (physical_prox_transport (f := f) (x := x) (p := p) hG hρ).mp hp
  have hb := proximalPoint_spec (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1)
    hf.lipschitz ((ρ / G) • x)
  have heq : (ρ / G) • p = proximalPoint 1 f ((ρ / G) • x) := by
    apply IsProxPoint.unique (by norm_num : (0 : ℝ) < 1) hf.weaklyConvex
    · simpa using ht
    · exact hb
  have hgbase := moreau_gradient_eq (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1) hf.lipschitz hf.weaklyConvex ((ρ / G) • x)
  rw [moreau_gradient_eq hρ hG.le hF.lipschitz hF.weaklyConvex]
  change (2 * ρ) • (x - p) = G • gradient (moreauEnvelope (1 / 2) f) ((ρ / G) • x)
  have hgbase' : gradient (moreauEnvelope (1 / 2) f) ((ρ / G) • x) =
      (2 : ℝ) • ((ρ / G) • x - proximalPoint 1 f ((ρ / G) • x)) := by
    simpa using hgbase
  rw [hgbase', ← heq, ← smul_sub, smul_smul, smul_smul]
  congr 1
  field_simp

theorem physical_moreau_gradient_norm {G ρ Δ : ℝ} {f : E → ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hf : Admissible 1 1 Δ f) (x : E) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (scaleFunction (G ^ 2 / ρ) (ρ / G) f)) x‖ =
      G * ‖gradient (moreauEnvelope (1 / 2) f) ((ρ / G) • x)‖ := by
  rw [physical_moreau_gradient hG hρ hf, norm_smul, Real.norm_eq_abs, abs_of_pos hG]

end WC
