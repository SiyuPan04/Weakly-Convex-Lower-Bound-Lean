import WC.Basic
import Mathlib.Analysis.Convex.Strong

/-! Genuine regularity under a possibly rank-deficient linear contraction,
as used for response maps defined on every orthonormal prefix. -/

noncomputable section
namespace WC

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem WeaklyConvex.precomp_contraction {ρ : ℝ} {f : F → ℝ}
    (hf : WeaklyConvex ρ f) (hρ : 0 ≤ ρ) (L : E →ₗ[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) :
    WeaklyConvex ρ (fun x => f (L x)) := by
  have hs : StrongConvexOn Set.univ (-ρ) f := by
    apply strongConvexOn_iff_convex.mpr
    apply hf.congr
    intro x _
    ring
  have ht : StrongConvexOn Set.univ (-ρ) (fun x => f (L x)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h := hs.2 (Set.mem_univ (L x)) (Set.mem_univ (L y)) ha hb hab
    have hn := hL (x - y)
    rw [map_sub] at hn
    have hsq : ‖L x - L y‖ ^ 2 ≤ ‖x - y‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    have hprod := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ a * b * ρ / 2 by positivity)
    simp only [StrongConvexOn, smul_eq_mul, map_add, map_smul] at h ⊢
    nlinarith
  have hc := strongConvexOn_iff_convex.mp ht
  apply hc.congr
  intro x _
  ring

theorem GloballyLipschitz.precomp_contraction {G : ℝ} {f : F → ℝ}
    (hf : GloballyLipschitz G f) (hG : 0 ≤ G) (L : E →ₗ[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) :
    GloballyLipschitz G (fun x => f (L x)) := by
  intro x y
  have hn := hL (x - y)
  rw [map_sub] at hn
  exact (hf (L x) (L y)).trans (mul_le_mul_of_nonneg_left hn hG)

theorem GapBound.precomp_linear {Δ : ℝ} {f : F → ℝ}
    (hf : GapBound Δ f) (L : E →ₗ[ℝ] F) : GapBound Δ (fun x => f (L x)) := by
  intro x
  simpa only [map_zero] using hf (L x)

theorem Admissible.precomp_contraction {G ρ Δ : ℝ} {f : F → ℝ}
    (hf : Admissible G ρ Δ f) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (L : E →ₗ[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) :
    Admissible G ρ Δ (fun x => f (L x)) :=
  ⟨hf.weaklyConvex.precomp_contraction hρ L hL,
    hf.lipschitz.precomp_contraction hG L hL, hf.gap.precomp_linear L⟩

end WC
