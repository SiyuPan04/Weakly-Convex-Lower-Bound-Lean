import WC.Basic
import Mathlib.Tactic.FieldSimp

/-!
Exact change of variables in proximal minimization (Lemma `lem:scaling`).
This file proves minimizer transport and the residual identity. It does not
silently identify the residual with an analytic derivative.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticObjective (μ : ℝ) (f : E → ℝ) (x y : E) : ℝ :=
  f y + μ * ‖x - y‖ ^ 2

def IsQuadraticMinimizer (μ : ℝ) (f : E → ℝ) (x p : E) : Prop :=
  ∀ y, quadraticObjective μ f x p ≤ quadraticObjective μ f x y

theorem quadraticObjective_scale {a b μ : ℝ} (hb : 0 ≤ b)
    (f : E → ℝ) (x y : E) :
    quadraticObjective (a * b ^ 2 * μ) (scaleFunction a b f) x y =
      a * quadraticObjective μ f (b • x) (b • y) := by
  simp only [quadraticObjective, scaleFunction, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hb]
  ring

theorem quadraticMinimizer_scale_iff {a b μ : ℝ} {f : E → ℝ} {x p : E}
    (ha : 0 < a) (hb : 0 < b) :
    IsQuadraticMinimizer (a * b ^ 2 * μ) (scaleFunction a b f) x p ↔
      IsQuadraticMinimizer μ f (b • x) (b • p) := by
  constructor
  · intro hp z
    have h := hp (b⁻¹ • z)
    simp only [quadraticObjective_scale hb.le, smul_inv_smul₀ hb.ne'] at h
    nlinarith
  · intro hp y
    rw [quadraticObjective_scale hb.le, quadraticObjective_scale hb.le]
    exact mul_le_mul_of_nonneg_left (hp (b • y)) ha.le

omit [NormedSpace ℝ E] in
theorem proxObjective_eq_quadratic {ρ : ℝ} (hρ : ρ ≠ 0)
    (f : E → ℝ) (x y : E) :
    proxObjective (1 / (2 * ρ)) f x y = quadraticObjective ρ f x y := by
  dsimp [proxObjective, quadraticObjective]
  field_simp [hρ]

theorem physical_scaling_constants {G ρ : ℝ} (hG : G ≠ 0) (hρ : ρ ≠ 0) :
    (G ^ 2 / ρ) * (ρ / G) = G ∧
    (G ^ 2 / ρ) * (ρ / G) ^ 2 = ρ := by
  constructor <;> field_simp

theorem physical_admissible_scale {G ρ Δ : ℝ} {f : E → ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hf : Admissible 1 1 Δ f) :
    Admissible G ρ ((G ^ 2 / ρ) * Δ)
      (scaleFunction (G ^ 2 / ρ) (ρ / G) f) := by
  have ha : 0 ≤ G ^ 2 / ρ := le_of_lt (div_pos (sq_pos_of_pos hG) hρ)
  have hb : 0 ≤ ρ / G := le_of_lt (div_pos hρ hG)
  have h := admissible_scale ha hb hf
  obtain ⟨h1, h2⟩ := physical_scaling_constants hG.ne' hρ.ne'
  simpa only [mul_one, h1, h2] using h

theorem physical_quadraticObjective {G ρ : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (f : E → ℝ) (x y : E) :
    quadraticObjective ρ (scaleFunction (G ^ 2 / ρ) (ρ / G) f) x y =
      (G ^ 2 / ρ) * quadraticObjective 1 f ((ρ / G) • x) ((ρ / G) • y) := by
  have h := quadraticObjective_scale (μ := 1) (a := G ^ 2 / ρ)
    (div_pos hρ hG).le f x y
  obtain ⟨_, h2⟩ := physical_scaling_constants hG.ne' hρ.ne'
  simpa only [mul_one, h2] using h

theorem physical_prox_transport {G ρ : ℝ} {f : E → ℝ} {x p : E}
    (hG : 0 < G) (hρ : 0 < ρ) :
    IsProxPoint (1 / (2 * ρ)) (scaleFunction (G ^ 2 / ρ) (ρ / G) f) x p ↔
      IsProxPoint (1 / 2) f ((ρ / G) • x) ((ρ / G) • p) := by
  have h := quadraticMinimizer_scale_iff (μ := 1) (f := f) (x := x) (p := p)
    (div_pos (sq_pos_of_pos hG) hρ) (div_pos hρ hG)
  obtain ⟨_, h2⟩ := physical_scaling_constants hG.ne' hρ.ne'
  have hhalf : ∀ z w : E, proxObjective (1 / 2) f z w = quadraticObjective 1 f z w := by
    intro z w
    norm_num [proxObjective, quadraticObjective]
  simpa only [IsProxPoint, IsQuadraticMinimizer, mul_one, h2,
    proxObjective_eq_quadratic hρ.ne', hhalf]
    using h

theorem physical_residual_scale {G ρ : ℝ} (hG : G ≠ 0) (hρ : ρ ≠ 0)
    (x p : E) :
    proxResidual (1 / (2 * ρ)) x p =
      G • proxResidual (1 / 2) ((ρ / G) • x) ((ρ / G) • p) := by
  simp only [proxResidual, ← smul_sub, smul_smul]
  congr 1
  field_simp

end WC
