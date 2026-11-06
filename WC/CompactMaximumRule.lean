import WC.Oracle
import WC.SubgradientCalculus
import WC.CompactConvexHull
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-! The genuine complete subdifferential rule for a compact continuous maximum. -/

noncomputable section
namespace WC

open Filter Topology

variable {α E : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def compactMaximum (f : α → E → ℝ) (x : E) : ℝ := sSup (Set.range fun a => f a x)
def activeParameters (f : α → E → ℝ) (x : E) : Set α := {a | f a x = compactMaximum f x}
def activeSlopes (f : α → E → ℝ) (x : E) : Set E :=
  {v | ∃ a ∈ activeParameters f x, v ∈ subdifferential (f a) x}

omit [Nonempty α] [InnerProductSpace ℝ E] in
theorem compactMaximum_bddAbove {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2)) (x : E) :
    BddAbove (Set.range fun a => f a x) := by
  exact (isCompact_range (hc.comp (continuous_id.prodMk continuous_const))).bddAbove

omit [Nonempty α] [InnerProductSpace ℝ E] in
theorem branch_le_compactMaximum {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2)) (a : α) (x : E) :
    f a x ≤ compactMaximum f x := le_csSup (compactMaximum_bddAbove hc x) (Set.mem_range_self a)

omit [InnerProductSpace ℝ E] in
theorem activeParameters_nonempty {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2)) (x : E) : (activeParameters f x).Nonempty := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨a, le_antisymm (branch_le_compactMaximum hc a x) ?_⟩
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨b, rfl⟩; exact ha (Set.mem_univ b))

omit [InnerProductSpace ℝ E] in
theorem compactMaximum_lipschitz {G : ℝ} {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hlip : ∀ a, GloballyLipschitz G (f a)) : GloballyLipschitz G (compactMaximum f) := by
  have hupper (x y : E) : compactMaximum f x - compactMaximum f y ≤ G * ‖x - y‖ := by
    have hs : compactMaximum f x ≤ compactMaximum f y + G * ‖x - y‖ := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨a, rfl⟩
      have hf := (le_abs_self (f a x - f a y)).trans (hlip a x y)
      linarith [branch_le_compactMaximum hc a y]
    linarith
  intro x y
  apply abs_le.mpr
  constructor
  · have h := hupper y x
    rw [norm_sub_rev y x] at h
    linarith
  · exact hupper x y

theorem compactMaximum_weaklyConvex {ρ : ℝ} {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hwc : ∀ a, WeaklyConvex ρ (f a)) : WeaklyConvex ρ (compactMaximum f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hsup : compactMaximum f (a • x + b • y) ≤
      a * (compactMaximum f x + ρ / 2 * ‖x‖ ^ 2) +
      b * (compactMaximum f y + ρ / 2 * ‖y‖ ^ 2) - ρ / 2 * ‖a • x + b • y‖ ^ 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    have hk := (hwc k).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at hk
    have hx := mul_le_mul_of_nonneg_left (branch_le_compactMaximum hc k x) ha
    have hy := mul_le_mul_of_nonneg_left (branch_le_compactMaximum hc k y) hb
    linarith
  simp only [smul_eq_mul]
  linarith

omit [CompactSpace α] [Nonempty α] in
theorem parameterSubgradient_graph_isClosed {ρ : ℝ} {f : α → E → ℝ}
    (hρ : 0 ≤ ρ) (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hwc : ∀ a, WeaklyConvex ρ (f a)) :
    IsClosed {p : α × E × E | p.2.2 ∈ subdifferential (f p.1) p.2.1} := by
  have heq : {p : α × E × E | p.2.2 ∈ subdifferential (f p.1) p.2.1} =
      ⋂ y : E, {p : α × E × E | f p.1 p.2.1 + inner ℝ p.2.2 (y - p.2.1) -
        ρ / 2 * ‖y - p.2.1‖ ^ 2 ≤ f p.1 y} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, subdifferential_eq_weak p.2.1 hρ (hwc p.1),
      WeakSubgradient]
  rw [heq]
  apply isClosed_iInter
  intro y
  have hcx : Continuous (fun p : α × E × E => f p.1 p.2.1) :=
    hc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hcy : Continuous (fun p : α × E × E => f p.1 y) :=
    hc.comp (continuous_fst.prodMk continuous_const)
  have hx : Continuous (fun p : α × E × E => y - p.2.1) :=
    continuous_const.sub (continuous_fst.comp continuous_snd)
  exact isClosed_le ((hcx.add ((continuous_snd.comp continuous_snd).inner hx)).sub
    (continuous_const.mul (hx.norm.pow 2))) hcy

omit [Nonempty α] in
theorem activeSlopes_isCompact [ProperSpace E] {G ρ : ℝ} {f : α → E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hlip : ∀ a, GloballyLipschitz G (f a)) (hwc : ∀ a, WeaklyConvex ρ (f a)) (x : E) :
    IsCompact (activeSlopes f x) := by
  let K : Set (α × E) := (Set.univ ×ˢ Metric.closedBall 0 G) ∩
    {p | f p.1 x = compactMaximum f x ∧ p.2 ∈ subdifferential (f p.1) x}
  have hgraph : IsClosed {p : α × E | p.2 ∈ subdifferential (f p.1) x} :=
    (parameterSubgradient_graph_isClosed hρ hc hwc).preimage
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have hactive : IsClosed {p : α × E | f p.1 x = compactMaximum f x} :=
    isClosed_eq (hc.comp (continuous_fst.prodMk continuous_const)) continuous_const
  have hK : IsCompact K := (isCompact_univ.prod (isCompact_closedBall 0 G)).inter_right
    (hactive.inter hgraph)
  have heq : activeSlopes f x = Prod.snd '' K := by
    ext v
    constructor
    · rintro ⟨a, ha, hv⟩
      exact ⟨(a, v), ⟨⟨Set.mem_univ _, subdifferential_subset_closedBall x hG (hlip a) hv⟩,
        ha, hv⟩, rfl⟩
    · rintro ⟨⟨a, v⟩, ⟨_, ha, hv⟩, rfl⟩
      exact ⟨a, ha, hv⟩
  rw [heq]
  exact hK.image continuous_snd

omit [Nonempty α] in
theorem activeSlopes_subset_subdifferential {f : α → E → ℝ}
    (hc : Continuous (fun p : α × E => f p.1 p.2)) (x : E) :
    activeSlopes f x ⊆ subdifferential (compactMaximum f) x := by
  rintro v ⟨a, ha, hv⟩
  exact hv.contact (branch_le_compactMaximum hc a) ha

/-- The complete actual maximum rule; no active-slope formula is assumed. -/
theorem subdifferential_compactMaximum_eq_convexHull [ProperSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {G ρ : ℝ} {f : α → E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hc : Continuous (fun p : α × E => f p.1 p.2))
    (hlip : ∀ a, GloballyLipschitz G (f a)) (hwc : ∀ a, WeaklyConvex ρ (f a)) (x : E) :
    subdifferential (compactMaximum f) x = convexHull ℝ (activeSlopes f x) := by
  apply Set.Subset.antisymm
  · rw [← closedConvexHull_eq_convexHull_of_compact (activeSlopes_isCompact hG hρ hc hlip hwc x)]
    intro q hq
    by_contra hqout
    obtain ⟨l, c, hsep, hcq⟩ := geometric_hahn_banach_closed_point
      (convex_closedConvexHull (𝕜 := ℝ) (s := activeSlopes f x))
      (isClosed_closedConvexHull (𝕜 := ℝ) (s := activeSlopes f x)) hqout
    let d : E := (InnerProductSpace.toDual ℝ E).symm l
    have hinner (v : E) : inner ℝ v d = l v := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let z : ℕ → E := fun n => x + t n • d
    have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    choose a ha using fun n : ℕ => activeParameters_nonempty hc (z n)
    choose v hv using fun n : ℕ => subdifferential_nonempty (z n) hG hρ (hlip (a n)) (hwc (a n))
    let K : Set (α × E) := Set.univ ×ˢ Metric.closedBall 0 G
    have hK : IsCompact K := isCompact_univ.prod (isCompact_closedBall 0 G)
    have hseq (n : ℕ) : (a n, v n) ∈ K :=
      ⟨Set.mem_univ _, subdifferential_subset_closedBall (z n) hG (hlip (a n)) (hv n)⟩
    obtain ⟨p, _, φ, hφ, hp⟩ := hK.tendsto_subseq hseq
    have hap : Tendsto (a ∘ φ) atTop (𝓝 p.1) := by
      simpa only [Function.comp_def] using (continuous_fst.tendsto p).comp hp
    have hvp : Tendsto (v ∘ φ) atTop (𝓝 p.2) := by
      simpa only [Function.comp_def] using (continuous_snd.tendsto p).comp hp
    have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have htφ := ht0.comp hφ.tendsto_atTop
    have hzφ : Tendsto (z ∘ φ) atTop (𝓝 x) := by
      simpa only [z, Function.comp_def, zero_smul, add_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add
          (htφ.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))))
    have hFcont := (compactMaximum_lipschitz hc hlip).continuous hG
    have hfLimit : Tendsto (fun n => f (a (φ n)) (z (φ n))) atTop (𝓝 (f p.1 x)) :=
      hc.continuousAt.tendsto.comp (hap.prodMk_nhds hzφ)
    have hFLimit : Tendsto (fun n => f (a (φ n)) (z (φ n))) atTop (𝓝 (compactMaximum f x)) := by
      have heq : (fun n => f (a (φ n)) (z (φ n))) =
          (fun n => compactMaximum f (z (φ n))) := funext fun n => ha (φ n)
      rw [heq]
      exact hFcont.continuousAt.tendsto.comp hzφ
    have hactive : p.1 ∈ activeParameters f x := tendsto_nhds_unique hfLimit hFLimit
    have hsub : p.2 ∈ subdifferential (f p.1) x :=
      (parameterSubgradient_graph_isClosed hρ hc hwc).mem_of_tendsto
        (hap.prodMk_nhds (hzφ.prodMk_nhds hvp))
        (Filter.Eventually.of_forall fun n => hv (φ n))
    have hcompare (n : ℕ) : inner ℝ q d ≤ inner ℝ (v n) d + ρ * t n * ‖d‖ ^ 2 := by
      have hqw := (weakSubgradient_iff_frechet hρ (compactMaximum_weaklyConvex hc hwc)).mpr hq
      have hvw := (weakSubgradient_iff_frechet hρ (hwc (a n))).mpr (hv n)
      have hlow := hqw (z n)
      have hupp := hvw x
      have hdom := branch_le_compactMaximum hc (a n) x
      have hactive' : f (a n) (z n) = compactMaximum f (z n) := ha n
      rw [hactive'] at hupp
      have hzx : z n - x = t n • d := by dsimp [z]; module
      have hxz : x - z n = -(t n • d) := by dsimp [z]; module
      rw [hzx] at hlow
      rw [hxz] at hupp
      simp only [real_inner_smul_right, inner_neg_right, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (htpos n)] at hlow hupp
      have hmul : t n * inner ℝ q d ≤ t n * (inner ℝ (v n) d + ρ * t n * ‖d‖ ^ 2) := by
        nlinarith
      exact (mul_le_mul_iff_right₀ (htpos n)).mp hmul
    have hlim : Tendsto (fun n => inner ℝ (v (φ n)) d + ρ * t (φ n) * ‖d‖ ^ 2)
        atTop (𝓝 (inner ℝ p.2 d)) := by
      simpa only [Function.comp_def, mul_zero, zero_mul, add_zero] using
        (hvp.inner tendsto_const_nhds).add
          ((tendsto_const_nhds.mul htφ).mul tendsto_const_nhds)
    have hle : inner ℝ q d ≤ inner ℝ p.2 d := ge_of_tendsto hlim
      (Filter.Eventually.of_forall fun n => hcompare (φ n))
    rw [hinner, hinner] at hle
    have hsep' := hsep p.2 (subset_closedConvexHull ⟨p.1, hactive, hsub⟩)
    linarith
  · exact convexHull_min (activeSlopes_subset_subdifferential hc x)
      (subdifferential_convex x hρ (compactMaximum_weaklyConvex hc hwc))

end WC
