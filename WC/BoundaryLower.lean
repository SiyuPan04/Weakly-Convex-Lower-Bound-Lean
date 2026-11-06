import WC.LowerReduction
import WC.SubgradientCalculus
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul

/-! Actual norm-cone certificates for the boundary parameter regimes. -/

noncomputable section
namespace WC
namespace BoundaryLower

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normCone (v : ℝ) (c : E) (x : E) : ℝ := v * ‖x - c‖

theorem normCone_convex {v : ℝ} (hv : 0 ≤ v) (c : E) :
    ConvexOn ℝ Set.univ (normCone v c) := by
  have hnorm : ConvexOn ℝ Set.univ (fun x : E => ‖x - c‖) := by
    simpa only [sub_eq_add_neg, Set.preimage_univ, Function.comp_def, add_comm] using
      (convexOn_norm (E := E) convex_univ).translate_right (-c)
  exact hnorm.smul hv

theorem normCone_weaklyConvex {v ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρ) (c : E) :
    WeaklyConvex ρ (normCone v c) := by
  have hnorm : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  exact (normCone_convex hv c).add (hnorm.smul (show 0 ≤ ρ / 2 by positivity))

omit [InnerProductSpace ℝ E] in
theorem normCone_lipschitz {v : ℝ} (hv : 0 ≤ v) (c : E) : GloballyLipschitz v (normCone v c) := by
  intro x y
  have h := abs_norm_sub_norm_le (x - c) (y - c)
  have hid : (x - c) - (y - c) = x - y := by module
  rw [hid] at h
  have hm := mul_le_mul_of_nonneg_left h hv
  simpa only [normCone, ← mul_sub, abs_mul, abs_of_nonneg hv] using hm

omit [InnerProductSpace ℝ E] in
theorem normCone_gap {v Δ : ℝ} (hv : 0 ≤ v) (c : E) (hgap : v * ‖c‖ ≤ Δ) :
    GapBound Δ (normCone v c) := by
  intro x
  have hx : 0 ≤ normCone v c x := mul_nonneg hv (norm_nonneg _)
  simpa only [normCone, zero_sub, norm_neg] using sub_le_iff_le_add.mpr (by linarith : v * ‖c‖ ≤ Δ + normCone v c x)

theorem normCone_tip_support {v ρ : ℝ} (hρ : 0 ≤ ρ) (c w : E) (hw : ‖w‖ ≤ v) :
    WeakSubgradient ρ (normCone v c) c w := by
  intro y
  have hi := (real_inner_le_norm w (y - c)).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  simp only [normCone, sub_self, norm_zero, mul_zero, zero_add]
  nlinarith [mul_nonneg hρ (sq_nonneg ‖y - c‖)]

variable [CompleteSpace E]

theorem normCone_gradient_at {v : ℝ} (c x : E) (hxc : x ≠ c) :
    HasGradientAt (normCone v c) ((v / ‖x - c‖) • (x - c)) x := by
  have h := hasGradientAt_distance_penalty (L := v) (x := c) (y := x) hxc.symm
  have hfun : (fun z : E => v * ‖c - z‖) = normCone v c := by funext z; simp [normCone, norm_sub_rev]
  rw [hfun] at h
  have hvec : (-v / ‖c - x‖) • (c - x) = (v / ‖x - c‖) • (x - c) := by
    rw [norm_sub_rev c x, show c - x = -(x - c) by module, smul_neg, ← neg_smul]
    congr 1
    ring
  rwa [hvec] at h

theorem normCone_subgradient_norm {v : ℝ} (hv : 0 ≤ v) {c x w : E} (hxc : x ≠ c)
    (hw : FrechetSubgradient (normCone v c) x w) : ‖w‖ = v := by
  rw [hw.eq_gradient (normCone_gradient_at c x hxc), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hv (norm_nonneg _))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxc))

theorem normCone_stationary_iff [ProperSpace E] {v ρ ε : ℝ}
    (hv : 0 < v) (hρ : 0 < ρ) (hεv : ε < v) (c x : E) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v c)) x‖ ≤ ε ↔
      ‖x - c‖ ≤ ε / (2 * ρ) := by
  let p := proximalPoint ρ (normCone v c) x
  have hlip := normCone_lipschitz hv.le c
  have hwc := normCone_weaklyConvex hv.le hρ.le c
  have hp := proximalPoint_spec hρ hv.le hlip x
  have hgrad := moreau_gradient_eq hρ hv.le hlip hwc x
  have hgradnorm : ‖gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v c)) x‖ =
      2 * ρ * ‖x - p‖ := by
    rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity)]
  constructor
  · intro hsmall
    have hpc : p = c := by
      by_contra hne
      have hs := (hp.weakSubgradient hρ hwc).frechet hρ.le
      have hn := normCone_subgradient_norm hv.le hne hs
      have heq : ‖gradient (moreauEnvelope (1 / (2 * ρ)) (normCone v c)) x‖ = v := by
        rw [hgrad]
        exact hn
      linarith
    rw [hpc] at hgradnorm
    apply (le_div_iff₀ (show 0 < 2 * ρ by positivity)).mpr
    nlinarith
  · intro hdist
    have hnorm : ‖(2 * ρ) • (x - c)‖ ≤ v := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity)]
      have hmul := (le_div_iff₀ (show 0 < 2 * ρ by positivity)).mp hdist
      nlinarith
    have htip := (normCone_tip_support hρ.le c ((2 * ρ) • (x - c)) hnorm).isProxPoint hρ
    have hpc : p = c := hp.unique hρ hwc htip
    rw [hgradnorm, hpc]
    have hmul := (le_div_iff₀ (show 0 < 2 * ρ by positivity)).mp hdist
    nlinarith

def coneVelocity (G ε : ℝ) : ℝ := min G (3 * ε / 2)
def coneOffset (ρ G ε : ℝ) : ℝ := ε ^ 2 / (ρ * coneVelocity G ε)

theorem coneVelocity_bounds {G ε : ℝ} (hε : 0 < ε) (hεG : ε < G) :
    ε < coneVelocity G ε ∧ coneVelocity G ε ≤ G ∧ coneVelocity G ε ≤ 3 * ε / 2 := by
  refine ⟨lt_min hεG (by linarith), min_le_left _ _, min_le_right _ _⟩

omit [CompleteSpace E] in
theorem cone_certificate {G ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (u : E) (hu : ‖u‖ = 1) :
    let v := coneVelocity G ε
    let a := coneOffset ρ G ε
    Admissible G ρ (ε ^ 2 / ρ) (normCone v (a • u)) ∧
      0 < a ∧ (ε / (2 * ρ)) / a ≤ 3 / 4 := by
  dsimp only
  obtain ⟨hεv, hvG, hvε⟩ := coneVelocity_bounds hε hεG
  have hv : 0 < coneVelocity G ε := lt_trans hε hεv
  have ha : 0 < coneOffset ρ G ε := div_pos (sq_pos_of_pos hε) (mul_pos hρ hv)
  have hva : coneVelocity G ε * coneOffset ρ G ε = ε ^ 2 / ρ := by
    dsimp [coneOffset]
    field_simp
  refine ⟨⟨normCone_weaklyConvex hv.le hρ.le _, ?_, ?_⟩, ha, ?_⟩
  · intro x y
    exact (normCone_lipschitz hv.le _ x y).trans
      (mul_le_mul_of_nonneg_right hvG (norm_nonneg _))
  · apply normCone_gap hv.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one, hva]
  · have heq : (ε / (2 * ρ)) / coneOffset ρ G ε = coneVelocity G ε / (2 * ε) := by
      dsimp [coneOffset]
      field_simp
    rw [heq]
    apply (div_le_iff₀ (show 0 < 2 * ε by positivity)).mpr
    linarith

theorem cone_origin_not_stationary [ProperSpace E] {G ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G) (u : E) (hu : ‖u‖ = 1) :
    ε < ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (normCone (coneVelocity G ε) (coneOffset ρ G ε • u))) 0‖ := by
  obtain ⟨hεv, _, _⟩ := coneVelocity_bounds hε hεG
  obtain ⟨_, ha, hratio⟩ := cone_certificate hρ hε hεG u hu
  have hrad := (div_le_iff₀ ha).mp hratio
  apply lt_of_not_ge
  intro hs
  have hdist := (normCone_stationary_iff (lt_trans hε hεv) hρ hεv
    (coneOffset ρ G ε • u) (0 : E)).mp hs
  simp only [zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one] at hdist
  nlinarith

theorem exists_nonstationary_origin {G ρ Δ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G) (hgap : ε ^ 2 / ρ ≤ Δ) :
    ∃ I : Model.Instance G ρ Δ,
      ε < ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective) 0‖ := by
  let u : Model.Space 1 := EuclideanSpace.basisFun (Fin 1) ℝ ⟨0, by decide⟩
  have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.norm_eq_one _
  have hf := (cone_certificate hρ hε hεG u hu).1
  refine ⟨⟨1, normCone (coneVelocity G ε) (coneOffset ρ G ε • u),
    ⟨hf.weaklyConvex, hf.lipschitz, hf.gap.mono hgap⟩⟩, ?_⟩
  exact cone_origin_not_stationary hρ hε hεG u hu

/-- The fixed initialization prevents a zero-call guarantee throughout the principal range. -/
theorem zero_call_lower_bound {G ρ Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (hgap : ε ^ 2 / ρ ≤ Δ) (hν : ν < 1) :
    (1 : ℝ≥0∞) ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  suffices (((0 + 1 : ℕ) : ℝ≥0∞) ≤ Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le) by
    simpa only [Nat.zero_add, Nat.cast_one] using this
  apply Model.oracleComplexity_lower_bound hG.le hρ.le 0
  intro A
  obtain ⟨I, hI⟩ := exists_nonstationary_origin hρ hε hεG hgap
  refine ⟨I, ?_⟩
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  have hevent : {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (Model.trajectory hG.le hρ.le A I seed 0)‖ ≤ ε} = ∅ := by
    ext seed
    simp only [Model.trajectory_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt hI
  have hzero : Model.successProbability hG.le hρ.le A I ε 0 = 0 := by
    unfold Model.successProbability
    rw [hevent]
    simp
  rw [hzero]
  exact ENNReal.ofReal_pos.mpr (by linarith)

end BoundaryLower
end WC
