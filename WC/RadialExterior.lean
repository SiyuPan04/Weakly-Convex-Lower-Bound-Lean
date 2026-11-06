import WC.Moreau
import WC.Oracle
import WC.SubgradientCalculus
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul

/-! Global radial regularity and exterior control for the final function's
own Moreau gradient. The interior stationarity barrier is a separate theorem. -/

noncomputable section
namespace WC

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialBranch (f : E → ℝ) (R : ℝ) (x : E) : ℝ := f 0 + 3 * (‖x‖ - R)

def radialWall (f : E → ℝ) (R : ℝ) (x : E) : ℝ := max (f x) (radialBranch f R x)

theorem GloballyLipschitz.mono {G K : ℝ} {f : E → ℝ}
    (hf : GloballyLipschitz G f) (hGK : G ≤ K) : GloballyLipschitz K f :=
  fun x y => (hf x y).trans (mul_le_mul_of_nonneg_right hGK (norm_nonneg _))

theorem GloballyLipschitz.max {G : ℝ} {f g : E → ℝ}
    (hf : GloballyLipschitz G f) (hg : GloballyLipschitz G g) :
    GloballyLipschitz G (fun x => max (f x) (g x)) := by
  intro x y
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hf x y) (hg x y))

theorem radialBranch_lipschitz (f : E → ℝ) (R : ℝ) : GloballyLipschitz 3 (radialBranch f R) := by
  intro x y
  have h := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by norm_num : (0 : ℝ) ≤ 3)
  have heq : radialBranch f R x - radialBranch f R y = 3 * (‖x‖ - ‖y‖) := by
    dsimp [radialBranch]; ring
  rw [heq, abs_mul]
  simpa using h

theorem radialWall_lipschitz {f : E → ℝ} (hf : GloballyLipschitz 2 f) (R : ℝ) :
    GloballyLipschitz 3 (radialWall f R) :=
  (hf.mono (by norm_num)).max (radialBranch_lipschitz f R)

theorem WeaklyConvex.max {ρ : ℝ} {f g : E → ℝ}
    (hf : WeaklyConvex ρ f) (hg : WeaklyConvex ρ g) :
    WeaklyConvex ρ (fun x => max (f x) (g x)) := by
  apply (hf.sup hg).congr
  intro x _
  change Max.max (f x + ρ / 2 * ‖x‖ ^ 2) (g x + ρ / 2 * ‖x‖ ^ 2) =
    Max.max (f x) (g x) + ρ / 2 * ‖x‖ ^ 2
  by_cases h : f x ≤ g x
  · have hh : f x + ρ / 2 * ‖x‖ ^ 2 ≤ g x + ρ / 2 * ‖x‖ ^ 2 := by linarith
    rw [max_eq_right h, max_eq_right hh]
  · have h' := le_of_not_ge h
    have hh : g x + ρ / 2 * ‖x‖ ^ 2 ≤ f x + ρ / 2 * ‖x‖ ^ 2 := by linarith
    rw [max_eq_left h', max_eq_left hh]

theorem radialBranch_weaklyConvex {ρ : ℝ} (hρ : 0 ≤ ρ) (f : E → ℝ) (R : ℝ) :
    WeaklyConvex ρ (radialBranch f R) := by
  have hn : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hrad : ConvexOn ℝ Set.univ (radialBranch f R) := by
    apply ((convexOn_univ_norm.smul (by norm_num : (0 : ℝ) ≤ 3)).add_const (f 0 - 3 * R)).congr
    intro x _
    dsimp [radialBranch]
    ring
  exact hrad.add (hn.smul (by positivity : (0 : ℝ) ≤ ρ / 2))

theorem radialWall_weaklyConvex {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 ≤ ρ) (hf : WeaklyConvex ρ f) (R : ℝ) : WeaklyConvex ρ (radialWall f R) :=
  hf.max (radialBranch_weaklyConvex hρ f R)

theorem radialBranch_dominates {f : E → ℝ} (hf : GloballyLipschitz 2 f) {R : ℝ} {x : E}
    (hx : 3 * R < ‖x‖) : f x < radialBranch f R x := by
  have hb := (le_abs_self (f x - f 0)).trans (hf x 0)
  simp only [sub_zero] at hb
  dsimp [radialBranch]
  linarith

theorem radialWall_eq_outside {f : E → ℝ} (hf : GloballyLipschitz 2 f) {R : ℝ} {x : E}
    (hx : 3 * R < ‖x‖) : radialWall f R x = radialBranch f R x :=
  max_eq_right (radialBranch_dominates hf hx).le

variable [CompleteSpace E]

theorem radialWall_eventuallyEq {f : E → ℝ} (hf : GloballyLipschitz 2 f) {R : ℝ} {x : E}
    (hx : 3 * R < ‖x‖) : radialWall f R =ᶠ[𝓝 x] radialBranch f R := by
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact radialWall_eq_outside hf hy

theorem radialBranch_hasGradientAt {f : E → ℝ} {R : ℝ} {x : E} (hx : x ≠ 0) :
    HasGradientAt (radialBranch f R) ((3 / ‖x‖) • x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (((hasGradientAt_norm_of_ne_zero hx).hasFDerivAt.sub_const R).const_mul 3).const_add (f 0)
  convert! h using 1
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply, real_inner_smul_left, smul_eq_mul]
  ring

theorem radialWall_subgradient_outside {f : E → ℝ} (hf : GloballyLipschitz 2 f)
    {R : ℝ} (hR : 0 < R) {x v : E} (hx : 3 * R < ‖x‖) :
    FrechetSubgradient (radialWall f R) x v ↔ v = (3 / ‖x‖) • x := by
  rw [frechetSubgradient_congr_eventuallyEq (radialWall_eventuallyEq hf hx)]
  apply frechetSubgradient_iff_gradient
  apply radialBranch_hasGradientAt
  exact norm_pos_iff.mp (by linarith)

theorem radialWall_moreau_exterior [ProperSpace E] {f : E → ℝ}
    (hlip : GloballyLipschitz 2 f) (hwc : WeaklyConvex (9 / 2 : ℝ) f)
    {R : ℝ} (hR : 1 ≤ R) {x : E} (hx : 4 * R ≤ ‖x‖) :
    ‖gradient (moreauEnvelope (1 / 9) (radialWall f R)) x‖ = 3 := by
  let H := radialWall f R
  let p := proximalPoint (9 / 2) H x
  have hHlip : GloballyLipschitz 3 H := radialWall_lipschitz hlip R
  have hHwc : WeaklyConvex (9 / 2 : ℝ) H := radialWall_weaklyConvex (by norm_num) hwc R
  have hp := proximalPoint_spec (by norm_num : (0 : ℝ) < 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 3) hHlip x
  have hdist := hp.displacement_le (by norm_num) (by norm_num) hHwc hHlip
  have hnorm := norm_sub_norm_le x p
  have hpout : 3 * R < ‖p‖ := by
    change ‖x - p‖ ≤ 3 / (2 * (9 / 2)) at hdist
    norm_num at hdist
    linarith
  have hsub := (hp.weakSubgradient (by norm_num) hHwc).frechet (by norm_num)
  have heq := (radialWall_subgradient_outside hlip (by linarith : 0 < R) hpout).mp hsub
  have hg := moreau_gradient_eq (by norm_num : (0 : ℝ) < 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 3) hHlip hHwc x
  have hp_norm_pos : 0 < ‖p‖ := by linarith
  norm_num at hg heq
  rw [hg, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hp_norm_pos)]
  exact div_mul_cancel₀ 3 hp_norm_pos.ne'

end WC
