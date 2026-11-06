import WC.MajorantAnalysis
import WC.SubgradientCalculus

/-! Actual source sets, their compactness, and the singleton subdifferential
at every remote source, from Lemma `newrand:sources`. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def majorantSources (f : E → ℝ) (L : ℝ) (x : E) : Set E :=
  {y | sourcePayoff f L x y = lipschitzMajorant f L x}

theorem majorantSources_nonempty [ProperSpace E] {f : E → ℝ} {L c A : ℝ} (u : E)
    (hc : 0 ≤ c) (hcL : c < L) (hf : Continuous f)
    (hgrowth : ∀ y, f y ≤ A + c * ‖u - y‖) (x : E) :
    (majorantSources f L x).Nonempty :=
  majorant_source_exists u hc hcL hf hgrowth x

theorem majorantSources_isClosed {f : E → ℝ} {L : ℝ}
    (hf : Continuous f) (x : E) : IsClosed (majorantSources f L x) :=
  isClosed_eq (hf.sub (continuous_const.mul (continuous_const.sub continuous_id).norm))
    continuous_const

theorem majorantSources_isCompact [ProperSpace E] {f : E → ℝ} {L c A : ℝ} (u : E)
    (hc : 0 ≤ c) (hcL : c < L) (hf : Continuous f)
    (hgrowth : ∀ y, f y ≤ A + c * ‖u - y‖) (x : E) :
    IsCompact (majorantSources f L x) := by
  have hfinite := majorant_finite_of_growth u hc hcL.le hgrowth
  let R := (A + c * ‖u - x‖ - f x) / (L - c)
  apply (isCompact_closedBall x R).of_isClosed_subset (majorantSources_isClosed hf x)
  intro y hy
  have htri : ‖u - y‖ ≤ ‖u - x‖ + ‖x - y‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (u - x) (x - y)
  have hm := mul_le_mul_of_nonneg_left htri hc
  have hdiff : f y - f x ≤ c * ‖x - y‖ + (A + c * ‖u - x‖ - f x) := by
    linarith [hgrowth y]
  have hr := source_radius_bound hfinite hy hdiff
  have hnorm : ‖x - y‖ ≤ R := by
    apply (le_div_iff₀ (sub_pos.mpr hcL)).mpr
    nlinarith
  simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev y x] using hnorm

theorem majorant_contact_subgradient {f : E → ℝ} {ρ L : ℝ} {x y v : E}
    (hL : 0 ≤ L) (hfinite : MajorantFinite f L) (hy : y ∈ majorantSources f L x)
    (hv : WeakSubgradient ρ f y v) : WeakSubgradient ρ (lipschitzMajorant f L) y v :=
  hv.contact (le_lipschitzMajorant hfinite) (majorant_source_contact hL hfinite hy).symm

variable [CompleteSpace E]

/-- At a remote source, every actual Fréchet subgradient equals the radial slope.
This proves the singleton assertion without assuming directional regularity. -/
theorem remote_source_subgradient {f : E → ℝ} {L : ℝ} {x y v : E}
    (hfinite : MajorantFinite f L) (hy : y ∈ majorantSources f L x) (hxy : x ≠ y)
    (hv : FrechetSubgradient f y v) : v = (-L / ‖x - y‖) • (x - y) := by
  let g := fun z : E => lipschitzMajorant f L x + L * ‖x - z‖
  have hfg : ∀ z, f z ≤ g z := by
    intro z
    have h := payoff_le_majorant hfinite x z
    dsimp [sourcePayoff] at h
    dsimp [g]
    linarith
  have hcontact : f y = g y := by
    change sourcePayoff f L x y = lipschitzMajorant f L x at hy
    dsimp [sourcePayoff] at hy
    dsimp [g]
    linarith
  have hs := hv.contact hfg hcontact
  have hg : HasGradientAt g ((-L / ‖x - y‖) • (x - y)) y := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    exact ((hasGradientAt_distance_penalty (L := L) hxy).hasFDerivAt).const_add _
  exact hs.eq_gradient hg

end WC
