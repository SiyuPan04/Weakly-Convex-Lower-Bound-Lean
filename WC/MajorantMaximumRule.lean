import WC.SourceSlopes
import WC.CompactConvexHull
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-!
# The full source maximum rule

The reverse inclusion is proved from actual nearby maximizing sources and
actual subgradients, using compactness and a translated payoff comparison.
-/

noncomputable section
namespace WC

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Upper comparison with any genuine subgradient at a source of the nearby point. -/
theorem source_directional_comparison {f : E → ℝ} {ρ L t : ℝ} {x d y v q : E}
    (hρ : 0 ≤ ρ) (hwc : WeaklyConvex ρ f) (hfinite : MajorantFinite f L)
    (ht : 0 < t) (hy : y ∈ majorantSources f L (x + t • d))
    (hv : v ∈ subdifferential f y)
    (hq : q ∈ subdifferential (lipschitzMajorant f L) x) :
    inner ℝ q d ≤ inner ℝ v d + ρ * t * ‖d‖ ^ 2 := by
  have hvw := (weakSubgradient_iff_frechet hρ hwc).mpr hv
  have hqw := (weakSubgradient_iff_frechet hρ (majorant_weaklyConvex hfinite hwc)).mpr hq
  have hlower := hqw (x + t • d)
  have hupper := hvw (y - t • d)
  have hpayoff := payoff_le_majorant hfinite x (y - t • d)
  change sourcePayoff f L (x + t • d) y = lipschitzMajorant f L (x + t • d) at hy
  have hdisp : x - (y - t • d) = (x + t • d) - y := by module
  have hsub : y - t • d - y = -(t • d) := by module
  dsimp [sourcePayoff] at hy hpayoff
  rw [hdisp] at hpayoff
  rw [hsub] at hupper
  simp only [add_sub_cancel_left, inner_neg_right, real_inner_smul_right,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hlower hupper
  have hmul : t * inner ℝ q d ≤ t * (inner ℝ v d + ρ * t * ‖d‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ ht).mp hmul

/-- The reverse source maximum rule, initially in the closed convex hull. -/
theorem subdifferential_majorant_subset_closedConvexHull [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {G ρ L Rs : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hL : 0 ≤ L)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hfinite : MajorantFinite f L)
    (hex : ∀ z, (majorantSources f L z).Nonempty)
    (hRs : ∀ z y, y ∈ majorantSources f L z → ‖z - y‖ ≤ Rs) (x : E) :
    subdifferential (lipschitzMajorant f L) x ⊆ closedConvexHull ℝ (sourceSlopes f L x) := by
  intro q hq
  by_contra hqout
  obtain ⟨l, c, hsep, hcq⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ) (s := sourceSlopes f L x))
    (isClosed_closedConvexHull (𝕜 := ℝ) (s := sourceSlopes f L x)) hqout
  let d : E := (InnerProductSpace.toDual ℝ E).symm l
  have hinner (v : E) : inner ℝ v d = l v := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let z : ℕ → E := fun n => x + t n • d
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htle (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    apply (div_le_one₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose y hy using fun n : ℕ => hex (z n)
  choose v hv using fun n : ℕ => subdifferential_nonempty (y n) hG hρ hlip hwc
  let K : Set (E × E) := Metric.closedBall x (Rs + ‖d‖) ×ˢ Metric.closedBall 0 G
  have hK : IsCompact K := (isCompact_closedBall x (Rs + ‖d‖)).prod (isCompact_closedBall 0 G)
  have hseq (n : ℕ) : (y n, v n) ∈ K := by
    constructor
    · have hs := hRs (z n) (y n) (hy n)
      have hz : ‖z n - x‖ ≤ ‖d‖ := by
        simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (htpos n)]
        exact (mul_le_mul_of_nonneg_right (htle n) (norm_nonneg d)).trans_eq (one_mul _)
      have htri : ‖y n - x‖ ≤ ‖z n - y n‖ + ‖z n - x‖ := by
        simpa only [sub_add_sub_cancel, norm_sub_rev (y n) (z n)] using
          norm_add_le (y n - z n) (z n - x)
      change dist (y n) x ≤ Rs + ‖d‖
      rw [dist_eq_norm]
      linarith
    · exact subdifferential_subset_closedBall (y n) hG hlip (hv n)
  obtain ⟨p, _, φ, hφ, hp⟩ := hK.tendsto_subseq hseq
  have hyp : Tendsto (y ∘ φ) atTop (𝓝 p.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto p).comp hp
  have hvp : Tendsto (v ∘ φ) atTop (𝓝 p.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto p).comp hp
  have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htφ : Tendsto (t ∘ φ) atTop (𝓝 (0 : ℝ)) := ht0.comp hφ.tendsto_atTop
  have hzφ : Tendsto (z ∘ φ) atTop (𝓝 x) := by
    simpa only [z, Function.comp_def, zero_smul, add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add
        (htφ.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))))
  have hfcont := hlip.continuous hG
  have hFcont := (majorant_lipschitz hL hfinite).continuous hL
  have hpaylim : Tendsto (fun n => sourcePayoff f L (z (φ n)) (y (φ n)))
      atTop (𝓝 (sourcePayoff f L x p.1)) := by
    exact (hfcont.continuousAt.tendsto.comp hyp).sub
      (tendsto_const_nhds.mul ((hzφ.sub hyp).norm))
  have hpaylimF : Tendsto (fun n => sourcePayoff f L (z (φ n)) (y (φ n)))
      atTop (𝓝 (lipschitzMajorant f L x)) := by
    have heq : (fun n => sourcePayoff f L (z (φ n)) (y (φ n))) =
        (fun n => lipschitzMajorant f L (z (φ n))) := by
      funext n
      exact hy (φ n)
    rw [heq]
    exact hFcont.continuousAt.tendsto.comp hzφ
  have hsource : p.1 ∈ majorantSources f L x := tendsto_nhds_unique hpaylim hpaylimF
  have hsub : p.2 ∈ subdifferential f p.1 :=
    (subdifferential_graph_isClosed hG hρ hlip hwc).mem_of_tendsto hp
      (Filter.Eventually.of_forall fun n => hv (φ n))
  have hlim : Tendsto (fun n => inner ℝ (v (φ n)) d + ρ * t (φ n) * ‖d‖ ^ 2)
      atTop (𝓝 (inner ℝ p.2 d)) := by
    simpa only [Function.comp_def, mul_zero, zero_mul, add_zero] using
      (hvp.inner tendsto_const_nhds).add
        ((tendsto_const_nhds.mul htφ).mul tendsto_const_nhds)
  have hle : inner ℝ q d ≤ inner ℝ p.2 d := ge_of_tendsto hlim
    (Filter.Eventually.of_forall fun n =>
      source_directional_comparison hρ hwc hfinite (htpos (φ n)) (hy (φ n)) (hv (φ n)) hq)
  rw [hinner, hinner] at hle
  have hsep' := hsep p.2 (subset_closedConvexHull ⟨p.1, hsource, hsub⟩)
  linarith

/-- Uniform source localization gives the compactness needed to remove closure. -/
theorem majorantSources_isCompact_of_radius [ProperSpace E]
    {f : E → ℝ} {G L Rs : ℝ} (hG : 0 ≤ G) (hlip : GloballyLipschitz G f)
    (hRs : ∀ z y, y ∈ majorantSources f L z → ‖z - y‖ ≤ Rs) (x : E) :
    IsCompact (majorantSources f L x) := by
  apply (isCompact_closedBall x Rs).of_isClosed_subset
    (majorantSources_isClosed (hlip.continuous hG) x)
  intro y hy
  simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev y x] using hRs x y hy

/-- The complete source maximum rule for the actual Lipschitz majorant. -/
theorem subdifferential_majorant_eq_convexHull [ProperSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {G ρ L Rs : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hL : 0 ≤ L)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (hfinite : MajorantFinite f L)
    (hex : ∀ z, (majorantSources f L z).Nonempty)
    (hRs : ∀ z y, y ∈ majorantSources f L z → ‖z - y‖ ≤ Rs) (x : E) :
    subdifferential (lipschitzMajorant f L) x = convexHull ℝ (sourceSlopes f L x) := by
  have hsources := majorantSources_isCompact_of_radius hG hlip hRs x
  have hslopes := sourceSlopes_isCompact hG hρ hlip hwc x hsources
  apply Set.Subset.antisymm
  · rw [← closedConvexHull_eq_convexHull_of_compact hslopes]
    exact subdifferential_majorant_subset_closedConvexHull hG hρ hL hlip hwc hfinite hex hRs x
  · exact sourceSlopes_convexHull_subset hρ hwc hfinite x

end WC
