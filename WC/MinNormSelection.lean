import WC.Oracle
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! The actual minimum-norm oracle selection and its Hausdorff continuity. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def minNormPoint (S : CompactConvexSets E) : E :=
  Classical.choose (S.val.isCompact.exists_isMinOn S.val.nonempty continuous_norm.continuousOn)

theorem minNormPoint_mem (S : CompactConvexSets E) : minNormPoint S ∈ (S.val : Set E) :=
  (Classical.choose_spec (S.val.isCompact.exists_isMinOn S.val.nonempty continuous_norm.continuousOn)).1

theorem minNormPoint_norm_le (S : CompactConvexSets E) {v : E} (hv : v ∈ (S.val : Set E)) :
    ‖minNormPoint S‖ ≤ ‖v‖ :=
  (Classical.choose_spec (S.val.isCompact.exists_isMinOn S.val.nonempty continuous_norm.continuousOn)).2 hv

theorem minNormPoint_variational (S : CompactConvexSets E) {v : E} (hv : v ∈ (S.val : Set E)) :
    0 ≤ inner ℝ (minNormPoint S) (v - minNormPoint S) := by
  let u := minNormPoint S
  have hmem : u ∈ (S.val : Set E) := minNormPoint_mem S
  letI : Nonempty (S.val : Set E) := ⟨⟨u, hmem⟩⟩
  have hi : ‖(0 : E) - u‖ = ⨅ w : (S.val : Set E), ‖(0 : E) - (w : E)‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      simpa only [zero_sub, norm_neg] using minNormPoint_norm_le S w.property
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        (⟨u, hmem⟩ : (S.val : Set E))
  have h := (norm_eq_iInf_iff_real_inner_le_zero S.property hmem).mp hi v hv
  simpa only [zero_sub, inner_neg_left, neg_nonpos] using h

theorem minNormPoint_norm_eq_infDist (S : CompactConvexSets E) :
    ‖minNormPoint S‖ = Metric.infDist (0 : E) (S.val : Set E) := by
  obtain ⟨v, hv, heq⟩ := S.val.isCompact.exists_infDist_eq_dist S.val.nonempty (0 : E)
  apply le_antisymm
  · rw [heq, dist_zero_left]
    exact minNormPoint_norm_le S hv
  · simpa only [dist_zero_left] using Metric.infDist_le_dist_of_mem (minNormPoint_mem S) (x := (0 : E))

theorem minNormPoint_unique (S : CompactConvexSets E) {v : E} (hv : v ∈ (S.val : Set E))
    (hmin : ∀ w ∈ (S.val : Set E), ‖v‖ ≤ ‖w‖) : v = minNormPoint S := by
  have hn : ‖v‖ = ‖minNormPoint S‖ :=
    le_antisymm (hmin _ (minNormPoint_mem S)) (minNormPoint_norm_le S hv)
  have hi := minNormPoint_variational S hv
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hi
  have hsq : ‖v - minNormPoint S‖ ^ 2 = 0 := by
    have hcomm : inner ℝ v (minNormPoint S) = inner ℝ (minNormPoint S) v := real_inner_comm _ _
    rw [norm_sub_sq_real, hcomm]
    have hnnonneg := sq_nonneg ‖v - minNormPoint S‖
    rw [norm_sub_sq_real, hcomm] at hnnonneg
    rw [hn] at hnnonneg ⊢
    nlinarith
  have hnormzero : ‖v - minNormPoint S‖ = 0 := by nlinarith [norm_nonneg (v - minNormPoint S)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)

theorem norm_minNormPoint_sub_le (S T : CompactConvexSets E) :
    |‖minNormPoint S‖ - ‖minNormPoint T‖| ≤ dist S T := by
  rw [minNormPoint_norm_eq_infDist, minNormPoint_norm_eq_infDist]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, Subtype.dist_eq] using
    (Metric.lipschitz_infDist_set (0 : E)).dist_le_mul S.val T.val

theorem minNormPoint_distance_sq_le (S T : CompactConvexSets E) :
    ‖minNormPoint S - minNormPoint T‖ ^ 2 ≤
      (‖minNormPoint S‖ + ‖minNormPoint T‖) * dist S T := by
  let u := minNormPoint S
  let v := minNormPoint T
  obtain ⟨a, ha, hda⟩ := S.val.isCompact.exists_infDist_eq_dist S.val.nonempty v
  obtain ⟨b, hb, hdb⟩ := T.val.isCompact.exists_infDist_eq_dist T.val.nonempty u
  have hcrossa : ‖a - v‖ ≤ dist S T := by
    have hlip := (Metric.lipschitz_infDist_set v).dist_le_mul S.val T.val
    rw [Metric.infDist_zero_of_mem (minNormPoint_mem T)] at hlip
    have hcross : Metric.infDist v (S.val : Set E) ≤ dist S T := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg,
        NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
    rw [hda] at hcross
    simpa only [dist_eq_norm, norm_sub_rev v a] using hcross
  have hcrossb : ‖b - u‖ ≤ dist S T := by
    have hlip := (Metric.lipschitz_infDist_set u).dist_le_mul T.val S.val
    rw [Metric.infDist_zero_of_mem (minNormPoint_mem S)] at hlip
    have hcross : Metric.infDist u (T.val : Set E) ≤ dist T S := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg,
        NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
    rw [hdb] at hcross
    simpa only [dist_eq_norm, norm_sub_rev u b, dist_comm T S] using hcross
  have hvaru := minNormPoint_variational S ha
  have hvarv := minNormPoint_variational T hb
  have h1 := (real_inner_le_norm u (a - v)).trans
    (mul_le_mul_of_nonneg_left hcrossa (norm_nonneg u))
  have h2 := (real_inner_le_norm v (b - u)).trans
    (mul_le_mul_of_nonneg_left hcrossb (norm_nonneg v))
  change ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) * dist S T
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hvaru hvarv h1 h2
  simp only [real_inner_comm] at hvaru hvarv h1 h2 ⊢
  nlinarith

theorem minNormPoint_continuous : Continuous (minNormPoint (E := E)) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let C : ℝ := 2 * ‖minNormPoint S‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := min 1 (ε ^ 2 / C)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (sq_pos_of_pos hε) hC)
  refine ⟨δ, hδ, ?_⟩
  intro T hTS
  have hdist1 : dist T S < 1 := hTS.trans_le (min_le_left _ _)
  have hdistε : dist T S < ε ^ 2 / C := hTS.trans_le (min_le_right _ _)
  have hnorm := norm_minNormPoint_sub_le T S
  have hsum : ‖minNormPoint T‖ + ‖minNormPoint S‖ ≤ C := by
    dsimp [C]
    have hu : ‖minNormPoint T‖ - ‖minNormPoint S‖ ≤ dist T S :=
      (le_abs_self _).trans hnorm
    linarith
  have hsq := minNormPoint_distance_sq_le T S
  have hbound := mul_le_mul_of_nonneg_right hsum (dist_nonneg : 0 ≤ dist T S)
  have hεsq : C * dist T S < ε ^ 2 := by
    have h := (lt_div_iff₀ hC).mp hdistε
    nlinarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (minNormPoint T - minNormPoint S)]

theorem minNormPoint_measurable [MeasurableSpace E] [BorelSpace E] :
    Measurable (minNormPoint (E := E)) := minNormPoint_continuous.measurable

def minimumNormSubgradient [ProperSpace E] [CompleteSpace E]
    {G ρ : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) (x : E) : E :=
  minNormPoint (fullSubdifferential hG hρ hlip hwc x)

theorem minimumNormSubgradient_mem [ProperSpace E] [CompleteSpace E]
    {G ρ : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) (x : E) :
    FrechetSubgradient f x (minimumNormSubgradient hG hρ hlip hwc x) :=
  minNormPoint_mem (fullSubdifferential hG hρ hlip hwc x)

theorem minimumNormSubgradient_measurable [ProperSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {G ρ : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) :
    Measurable (minimumNormSubgradient hG hρ hlip hwc) :=
  minNormPoint_measurable.comp (fullSubdifferential_measurable hG hρ hlip hwc)

/-- This is a function of the oracle reply alone, as required by the algorithm model. -/
def minimumNormReply (reply : ℝ × CompactConvexSets E) : E := minNormPoint reply.2

theorem minimumNormReply_measurable [MeasurableSpace E] [BorelSpace E] :
    Measurable (minimumNormReply (E := E)) := minNormPoint_measurable.comp measurable_snd

end WC
