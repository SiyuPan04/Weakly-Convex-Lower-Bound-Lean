import WC.Scaling
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Existence and uniqueness of the paper's proximal subproblem. These are
proved from the actual global Lipschitz and weak convexity properties.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem GloballyLipschitz.continuous {G : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hf : GloballyLipschitz G f) : Continuous f := by
  have hlip : LipschitzWith ⟨G, hG⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f x) (f y) ≤ G * dist x y
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hf x y
  exact hlip.continuous

theorem quadraticObjective_continuous {ρ G : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hf : GloballyLipschitz G f) (x : E) :
    Continuous (quadraticObjective ρ f x) := by
  exact (hf.continuous hG).add (continuous_const.mul
    ((continuous_const.sub continuous_id).norm.pow 2))

/-- A direct compact-ball proof of coercive proximal attainment. -/
theorem exists_quadraticMinimizer [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hf : GloballyLipschitz G f) (x : E) :
    ∃ p, IsQuadraticMinimizer ρ f x p := by
  let R : ℝ := 2 * G / ρ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx : x ∈ Metric.closedBall x R := by simp [hR]
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, hx⟩ (quadraticObjective_continuous hG hf x).continuousOn
  refine ⟨p, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall x R
  · exact hmin hy
  · have hdist : R < ‖x - y‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev y x, not_le] using hy
    have hnonneg := norm_nonneg (x - y)
    have hRG : G < ρ * ‖x - y‖ := by
      have ht := mul_lt_mul_of_pos_left hdist hρ
      dsimp [R] at ht
      have heq : ρ * (2 * G / ρ + 1) = 2 * G + ρ := by field_simp
      rw [heq] at ht
      linarith
    have hxy : f x - f y ≤ G * ‖x - y‖ :=
      (le_abs_self _).trans (hf x y)
    have hprod := mul_le_mul_of_nonneg_right hRG.le hnonneg
    have hcenter : quadraticObjective ρ f x x ≤ quadraticObjective ρ f x y := by
      simp only [quadraticObjective, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, add_zero]
      nlinarith
    exact (hmin hx).trans hcenter

theorem weaklyConvex_quadratic_strong {ρ : ℝ} {f : E → ℝ}
    (hf : WeaklyConvex ρ f) (x : E) :
    StrongConvexOn Set.univ ρ (quadraticObjective ρ f x) := by
  apply strongConvexOn_iff_convex.mpr
  have haff : ConvexOn ℝ Set.univ (fun y : E =>
      -2 * ρ * inner ℝ x y + ρ * ‖x‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b _ _ hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    have hconst : (a + b) * (ρ * ‖x‖ ^ 2) = ρ * ‖x‖ ^ 2 := by rw [hab, one_mul]
    nlinarith [hconst]
  have hadd := hf.add haff
  apply hadd.congr
  intro y _
  simp only [Pi.add_apply, quadraticObjective, norm_sub_sq_real]
  ring

theorem quadraticMinimizer_unique {ρ : ℝ} {f : E → ℝ} {x p q : E}
    (hρ : 0 < ρ) (hf : WeaklyConvex ρ f)
    (hp : IsQuadraticMinimizer ρ f x p) (hq : IsQuadraticMinimizer ρ f x q) : p = q := by
  have hs := weaklyConvex_quadratic_strong hf x
  have hm := hs.2 (Set.mem_univ p) (Set.mem_univ q)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpq : quadraticObjective ρ f x p = quadraticObjective ρ f x q :=
    le_antisymm (hp q) (hq p)
  have hp_mid := hp ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q)
  simp only [smul_eq_mul] at hm
  rw [hpq] at hp_mid hm
  have hn : ‖p - q‖ ^ 2 = 0 := by
    have hn := sq_nonneg ‖p - q‖
    nlinarith
  have hnorm : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem existsUnique_quadraticMinimizer [ProperSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E) :
    ∃! p, IsQuadraticMinimizer ρ f x p := by
  obtain ⟨p, hp⟩ := exists_quadraticMinimizer hρ hG hlip x
  exact ⟨p, hp, fun q hq => quadraticMinimizer_unique hρ hwc hq hp⟩

end WC
