import WC.MajorantSources
import WC.Oracle

/-! Compactness and supporting properties of all actual source slopes. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceSlopes (f : E → ℝ) (L : ℝ) (x : E) : Set E :=
  {v | ∃ y ∈ majorantSources f L x, v ∈ subdifferential f y}

theorem sourceSlopes_isCompact [ProperSpace E] {f : E → ℝ} {G ρ L : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E)
    (hsources : IsCompact (majorantSources f L x)) :
    IsCompact (sourceSlopes f L x) := by
  let K := (majorantSources f L x ×ˢ Metric.closedBall (0 : E) G) ∩
    {p : E × E | p.2 ∈ subdifferential f p.1}
  have hK : IsCompact K :=
    (hsources.prod (isCompact_closedBall 0 G)).inter_right
      (subdifferential_graph_isClosed hG hρ hlip hwc)
  have heq : sourceSlopes f L x = Prod.snd '' K := by
    ext v
    constructor
    · rintro ⟨y, hy, hv⟩
      refine ⟨(y, v), ⟨⟨hy, ?_⟩, hv⟩, rfl⟩
      exact subdifferential_subset_closedBall y hG hlip hv
    · rintro ⟨⟨y, w⟩, ⟨⟨hy, _⟩, hv⟩, rfl⟩
      exact ⟨y, hy, hv⟩
  rw [heq]
  exact hK.image continuous_snd

theorem sourceSlopes_nonempty [CompleteSpace E] {f : E → ℝ} {G ρ L : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x : E)
    (hsources : (majorantSources f L x).Nonempty) :
    (sourceSlopes f L x).Nonempty := by
  obtain ⟨y, hy⟩ := hsources
  obtain ⟨v, hv⟩ := subdifferential_nonempty y hG hρ hlip hwc
  exact ⟨v, y, hy, hv⟩

/-- A source branch is tangent to the majorant after translation. -/
theorem source_supports_majorant {f : E → ℝ} {ρ L : ℝ} {x y v : E}
    (hfinite : MajorantFinite f L) (hy : y ∈ majorantSources f L x)
    (hv : WeakSubgradient ρ f y v) : WeakSubgradient ρ (lipschitzMajorant f L) x v := by
  intro z
  have hs := payoff_le_majorant hfinite z (y + (z - x))
  have hg := hv (y + (z - x))
  have hdisp : z - (y + (z - x)) = x - y := by module
  have hpoint : y + (z - x) - y = z - x := by module
  change sourcePayoff f L x y = lipschitzMajorant f L x at hy
  dsimp [sourcePayoff] at hs hy
  rw [hdisp] at hs
  rw [hpoint] at hg
  linarith

theorem sourceSlopes_subset_subdifferential {f : E → ℝ} {ρ L : ℝ}
    (hρ : 0 ≤ ρ) (hwc : WeaklyConvex ρ f)
    (hfinite : MajorantFinite f L) (x : E) :
    sourceSlopes f L x ⊆ subdifferential (lipschitzMajorant f L) x := by
  rintro v ⟨y, hy, hv⟩
  exact (source_supports_majorant hfinite hy
    ((weakSubgradient_iff_frechet hρ hwc).mpr hv)).frechet hρ

theorem sourceSlopes_convexHull_subset {f : E → ℝ} {ρ L : ℝ}
    (hρ : 0 ≤ ρ) (hwc : WeaklyConvex ρ f)
    (hfinite : MajorantFinite f L) (x : E) :
    convexHull ℝ (sourceSlopes f L x) ⊆ subdifferential (lipschitzMajorant f L) x :=
  convexHull_min (sourceSlopes_subset_subdifferential hρ hwc hfinite x)
    (subdifferential_convex x hρ (majorant_weaklyConvex hfinite hwc))

variable [CompleteSpace E]

theorem source_support_equality {f : E → ℝ} {L : ℝ} {x y v : E}
    (hfinite : MajorantFinite f L) (hy : y ∈ majorantSources f L x)
    (hv : FrechetSubgradient f y v) :
    f y + inner ℝ v (x - y) = lipschitzMajorant f L x := by
  by_cases hxy : x = y
  · subst x
    simpa [majorantSources, sourcePayoff] using hy
  · have hv' := remote_source_subgradient hfinite hy hxy hv
    have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
    rw [hv', real_inner_smul_left, real_inner_self_eq_norm_sq]
    change sourcePayoff f L x y = lipschitzMajorant f L x at hy
    dsimp [sourcePayoff] at hy
    have heq : (-L / ‖x - y‖) * ‖x - y‖ ^ 2 = -L * ‖x - y‖ := by field_simp
    rw [heq]
    linarith

theorem source_subgradient_norm_le {f : E → ℝ} {ρ L : ℝ} {x y v : E}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hfinite : MajorantFinite f L)
    (hy : y ∈ majorantSources f L x) (hv : WeakSubgradient ρ f y v) : ‖v‖ ≤ L :=
  (majorant_contact_subgradient hL hfinite hy hv).norm_le hρ hL
    (majorant_lipschitz hL hfinite)

end WC
