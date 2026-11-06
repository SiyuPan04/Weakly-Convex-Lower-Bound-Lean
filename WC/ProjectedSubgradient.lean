import WC.Subgradient
import WC.Scaling
import WC.Numerics
import WC.Moreau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The actual projected subgradient step for proximal subproblems

The projection is the explicit radial projection onto a Euclidean closed ball.
Its feasibility and distance inequality are proved directly.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ballProject (x : E) (R : ℝ) (y : E) : E :=
  if ‖y - x‖ ≤ R then y else x + (R / ‖y - x‖) • (y - x)

theorem ballProject_mem {x y : E} {R : ℝ} (hR : 0 ≤ R) :
    ballProject x R y ∈ Metric.closedBall x R := by
  unfold ballProject
  split_ifs with hy
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  · have hr : 0 < ‖y - x‖ := lt_of_le_of_lt hR (lt_of_not_ge hy)
    have hratio : 0 ≤ R / ‖y - x‖ := div_nonneg hR hr.le
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hratio]
    exact le_of_eq (div_mul_cancel₀ R hr.ne')

theorem ballProject_eq_self {x y : E} {R : ℝ} (hy : y ∈ Metric.closedBall x R) :
    ballProject x R y = y := by
  unfold ballProject
  apply if_pos
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hy

/-- Radial projection cannot increase distance to any point in the ball. -/
theorem ballProject_distance_le {x y p : E} {R : ℝ} (hR : 0 ≤ R)
    (hp : p ∈ Metric.closedBall x R) : ‖ballProject x R y - p‖ ≤ ‖y - p‖ := by
  unfold ballProject
  split_ifs with hy
  · rfl
  · let v := y - x
    let w := p - x
    let r := ‖v‖
    let a := R / r
    have hr : 0 < r := lt_of_le_of_lt hR (lt_of_not_ge hy)
    have hRr : R < r := lt_of_not_ge hy
    have ha0 : 0 ≤ a := div_nonneg hR hr.le
    have ha1 : a ≤ 1 := (div_le_one₀ hr).mpr hRr.le
    have har : a * r = R := div_mul_cancel₀ _ hr.ne'
    have hwR : ‖w‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    have hi : inner ℝ v w ≤ r * R :=
      (real_inner_le_norm v w).trans (mul_le_mul_of_nonneg_left hwR hr.le)
    have hinner : 2 * (1 - a) * inner ℝ v w ≤ 2 * r * R - 2 * R ^ 2 := by
      calc
        _ ≤ 2 * (1 - a) * (r * R) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ = 2 * ((1 - a) * r) * R := by ring
        _ = 2 * (r - R) * R := by congr 2; nlinarith [har]
        _ = _ := by ring
    have hanorm : ‖a • v‖ ^ 2 = R ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
      change (a * r) ^ 2 = R ^ 2
      rw [har]
    have hsq : ‖a • v - w‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
      rw [norm_sub_sq_real (a • v) w, norm_sub_sq_real v w, hanorm, real_inner_smul_left]
      change R ^ 2 - 2 * (a * inner ℝ v w) + ‖w‖ ^ 2 ≤ r ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2
      nlinarith [sq_nonneg (r - R)]
    have hnorm : ‖a • v - w‖ ≤ ‖v - w‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hleft : x + (R / ‖y - x‖) • (y - x) - p = a • v - w := by dsimp [a, r, v, w]; module
    have hright : y - p = v - w := by dsimp [v, w]; module
    simpa only [hleft, hright] using hnorm

theorem quadratic_support_from_weakSubgradient {ρ : ℝ} {f : E → ℝ}
    {x z v : E} (hv : WeakSubgradient ρ f z v) (p : E) :
    quadraticObjective ρ f x z - quadraticObjective ρ f x p + ρ / 2 * ‖z - p‖ ^ 2 ≤
      inner ℝ (v + (2 * ρ) • (z - x)) (z - p) := by
  have hs := hv p
  dsimp [quadraticObjective]
  rw [norm_sub_sq_real x z, norm_sub_sq_real x p, norm_sub_sq_real z p]
  rw [norm_sub_sq_real p z] at hs
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at hs ⊢
  simp only [real_inner_comm]
  simp only [real_inner_comm] at hs
  nlinarith

def proximalSubgradientStep (x : E) (ρ G α : ℝ) (z v : E) : E :=
  ballProject x (G / ρ) (z - α • (v + (2 * ρ) • (z - x)))

theorem proximalSubgradient_norm_le {ρ G : ℝ} {f : E → ℝ} {x z v : E}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hv : WeakSubgradient ρ f z v) (hz : z ∈ Metric.closedBall x (G / ρ)) :
    ‖v + (2 * ρ) • (z - x)‖ ≤ 3 * G := by
  have hvnorm := hv.norm_le hρ.le hG hlip
  have hdist : ‖z - x‖ ≤ G / ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hmul := (le_div_iff₀ hρ).mp hdist
  have htri := norm_add_le v ((2 * ρ) • (z - x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * ρ)] at htri
  nlinarith

/-- The paper's weighted one-step inequality, for actual weak subgradients and actual projection. -/
theorem proximalSubgradient_weighted_recurrence {ρ G : ℝ} {f : E → ℝ} {x z p v : E}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hv : WeakSubgradient ρ f z v) (hz : z ∈ Metric.closedBall x (G / ρ))
    (hp : p ∈ Metric.closedBall x (G / ρ)) (j : ℕ) :
    (j : ℝ) * (quadraticObjective ρ f x z - quadraticObjective ρ f x p) ≤
      ρ / 4 * j * ((j : ℝ) - 1) * ‖z - p‖ ^ 2 -
      ρ / 4 * j * ((j : ℝ) + 1) *
        ‖proximalSubgradientStep x ρ G (2 / (ρ * ((j : ℝ) + 1))) z v - p‖ ^ 2 +
      (9 * G ^ 2 / ρ) * (j : ℝ) / ((j : ℝ) + 1) := by
  let α : ℝ := 2 / (ρ * ((j : ℝ) + 1))
  let u := v + (2 * ρ) • (z - x)
  have hα : 0 < α := by dsimp [α]; positivity
  have hu := proximalSubgradient_norm_le hρ hG hlip hv hz
  have hsupport := quadratic_support_from_weakSubgradient (x := x) hv p
  have hproject := ballProject_distance_le (y := z - α • u)
    (show 0 ≤ G / ρ by positivity) hp
  have hproject_sq : ‖ballProject x (G / ρ) (z - α • u) - p‖ ^ 2 ≤ ‖(z - p) - α • u‖ ^ 2 := by
    have hid : z - α • u - p = (z - p) - α • u := by module
    rw [hid] at hproject
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hproject
  rw [norm_sub_sq_real (z - p) (α • u), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hα] at hproject_sq
  have hinner : inner ℝ (z - p) u = inner ℝ u (z - p) := real_inner_comm _ _
  have hu_sq : ‖u‖ ^ 2 ≤ 9 * G ^ 2 := by
    change ‖u‖ ≤ 3 * G at hu
    nlinarith [norm_nonneg u]
  have hbound : 2 * α * (quadraticObjective ρ f x z - quadraticObjective ρ f x p) ≤
      (1 - α * ρ) * ‖z - p‖ ^ 2 -
      ‖ballProject x (G / ρ) (z - α • u) - p‖ ^ 2 + α ^ 2 * (9 * G ^ 2) := by
    have hs := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ 2 * α by positivity)
    have hu' := mul_le_mul_of_nonneg_left hu_sq (sq_nonneg α)
    change _ ≤ inner ℝ u (z - p) at hsupport
    nlinarith [hs, hu', hinner]
  have hfactor : 0 ≤ ρ * j * ((j : ℝ) + 1) / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbound hfactor
  change (j : ℝ) * (quadraticObjective ρ f x z - quadraticObjective ρ f x p) ≤ _
  dsimp [α, proximalSubgradientStep, u] at hmul ⊢
  have hρne : ρ ≠ 0 := hρ.ne'
  have hjne : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp at hmul ⊢
  nlinarith

theorem ballProject_measurable_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (R : ℝ) :
    Measurable (fun p : E × E => ballProject p.1 R p.2) := by
  unfold ballProject
  have hdiff : Measurable (fun p : E × E => p.2 - p.1) := measurable_snd.sub measurable_fst
  exact measurable_snd.ite (measurableSet_le hdiff.norm measurable_const)
    (measurable_fst.add ((measurable_const.div hdiff.norm).smul hdiff))

/-- The true proximal point is feasible for the paper's inner constraint ball. -/
theorem IsProxPoint.mem_proximalBall {ρ G : ℝ} {f : E → ℝ} {x p : E}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (hp : IsProxPoint (1 / (2 * ρ)) f x p) :
    p ∈ Metric.closedBall x (G / ρ) := by
  have hn := (hp.weakSubgradient hρ hwc).norm_le hρ.le hG hlip
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity),
    norm_sub_rev x p] at hn
  change dist p x ≤ G / ρ
  rw [dist_eq_norm]
  apply (le_div_iff₀ hρ).2
  nlinarith [mul_nonneg hρ.le (norm_nonneg (p - x))]

/-- Zero-based storage for the paper's `z₁,z₂,...`. -/
def proximalInnerIterate (x : E) (ρ G : ℝ) (select : E → E) : ℕ → E
  | 0 => x
  | k + 1 => proximalSubgradientStep x ρ G (2 / (ρ * ((k : ℝ) + 2)))
      (proximalInnerIterate x ρ G select k) (select (proximalInnerIterate x ρ G select k))

theorem proximalInnerIterate_mem {ρ G : ℝ} (x : E) (select : E → E)
    (hρ : 0 < ρ) (hG : 0 ≤ G) (k : ℕ) :
    proximalInnerIterate x ρ G select k ∈ Metric.closedBall x (G / ρ) := by
  cases k with
  | zero => simp [proximalInnerIterate, show 0 ≤ G / ρ by positivity]
  | succ k => exact ballProject_mem (show 0 ≤ G / ρ by positivity)

/-- The inner method's weighted error sum, derived from its actual iterates. -/
theorem proximalInnerIterate_weighted_error {ρ G : ℝ} {f : E → ℝ}
    (x p : E) (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z))
    (hp : p ∈ Metric.closedBall x (G / ρ)) (L : ℕ) :
    (∑ k ∈ Finset.range L, ((k : ℝ) + 1) *
      (quadraticObjective ρ f x (proximalInnerIterate x ρ G select k) - quadraticObjective ρ f x p)) ≤
      (9 * G ^ 2 / ρ) * L := by
  let z := proximalInnerIterate x ρ G select
  let C : ℝ := 9 * G ^ 2 / ρ
  let a : ℕ → ℝ := fun k => ρ / 4 * (k : ℝ) * ((k : ℝ) + 1) * ‖z k - p‖ ^ 2
  let Eerror : ℕ → ℝ := fun j => quadraticObjective ρ f x (z (j - 1)) - quadraticObjective ρ f x p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hstep (k : ℕ) (_ : k < L) :
      ((k : ℝ) + 1) * Eerror (k + 1) ≤ a k - a (k + 1) + C := by
    have hv := (weakSubgradient_iff_frechet hρ.le hwc).mpr (hselect (z k))
    have hr := proximalSubgradient_weighted_recurrence hρ hG hlip hv
      (proximalInnerIterate_mem x select hρ hG k) hp (k + 1)
    have hiter : proximalSubgradientStep x ρ G (2 / (ρ * (((k + 1 : ℕ) : ℝ) + 1)))
        (z k) (select (z k)) = z (k + 1) := by
      simp only [Nat.cast_add, Nat.cast_one]
      change proximalSubgradientStep x ρ G (2 / (ρ * ((k : ℝ) + 1 + 1)))
        (z k) (select (z k)) = proximalSubgradientStep x ρ G (2 / (ρ * ((k : ℝ) + 2)))
          (z k) (select (z k))
      have heq : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
      rw [heq]
    rw [hiter] at hr
    have hfrac : C * ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ C := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)).2
      nlinarith
    dsimp [Eerror, a, C] at hr hfrac ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hr ⊢
    have hden : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [hden] at hr
    nlinarith
  have ht := weighted_error_telescope L Eerror a C
    (by simp [a]) (by dsimp [a]; positivity) hstep
  simpa only [Eerror, Nat.add_sub_cancel, C] using ht

end WC
