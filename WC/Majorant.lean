import WC.Basic

/-!
The supremal Lipschitz majorant in equation `newrand:majorant`.
This proves the order, finiteness, and Lipschitz parts of Proposition
`prop:regularity` for any source function with subcritical linear growth.
Attainment, weak convexity, source subdifferentials and locality are separate
obligations; none of them is assumed or claimed in this file.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E]

def sourcePayoff (f : E → ℝ) (L : ℝ) (x y : E) : ℝ :=
  f y - L * ‖x - y‖

def lipschitzMajorant (f : E → ℝ) (L : ℝ) (x : E) : ℝ :=
  sSup (Set.range (sourcePayoff f L x))

def MajorantFinite (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x, BddAbove (Set.range (sourcePayoff f L x))

theorem majorant_finite_of_growth {f : E → ℝ} {L c A : ℝ} (u : E)
    (hc : 0 ≤ c) (hcL : c ≤ L) (hgrowth : ∀ y, f y ≤ A + c * ‖u - y‖) :
    MajorantFinite f L := by
  intro x
  refine ⟨A + c * ‖u - x‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hn : ‖u - y‖ ≤ ‖u - x‖ + ‖x - y‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (u - x) (x - y)
  have ht := mul_le_mul_of_nonneg_left hn hc
  have hL := mul_le_mul_of_nonneg_right hcL (norm_nonneg (x - y))
  dsimp [sourcePayoff]
  linarith [hgrowth y]

theorem le_lipschitzMajorant {f : E → ℝ} {L : ℝ}
    (hfinite : MajorantFinite f L) (x : E) : f x ≤ lipschitzMajorant f L x := by
  have h := le_csSup (hfinite x) (Set.mem_range_self x)
  simpa [sourcePayoff, lipschitzMajorant] using h

theorem payoff_le_majorant {f : E → ℝ} {L : ℝ}
    (hfinite : MajorantFinite f L) (x y : E) :
    sourcePayoff f L x y ≤ lipschitzMajorant f L x :=
  le_csSup (hfinite x) (Set.mem_range_self y)

theorem majorant_sub_le {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hfinite : MajorantFinite f L) (x z : E) :
    lipschitzMajorant f L x - lipschitzMajorant f L z ≤ L * ‖x - z‖ := by
  have hbound : lipschitzMajorant f L x ≤ lipschitzMajorant f L z + L * ‖x - z‖ := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨y, rfl⟩
    have hy := payoff_le_majorant hfinite z y
    have hn : ‖z - y‖ ≤ ‖x - z‖ + ‖x - y‖ := by
      simpa only [sub_add_sub_cancel, norm_sub_rev z x] using
        norm_add_le (z - x) (x - y)
    have ht := mul_le_mul_of_nonneg_left hn hL
    dsimp [sourcePayoff] at hy ⊢
    linarith
  linarith

theorem majorant_lipschitz {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hfinite : MajorantFinite f L) : GloballyLipschitz L (lipschitzMajorant f L) := by
  intro x z
  apply abs_le.mpr
  constructor
  · have h := majorant_sub_le hL hfinite z x
    rw [norm_sub_rev z x] at h
    linarith
  · exact majorant_sub_le hL hfinite x z

theorem majorant_le_of_lipschitz_majorizes {f g : E → ℝ} {L : ℝ}
    (hg : GloballyLipschitz L g) (hfg : ∀ x, f x ≤ g x) (x : E) :
    lipschitzMajorant f L x ≤ g x := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨y, rfl⟩
  have hy := (le_abs_self (g y - g x)).trans (hg y x)
  rw [norm_sub_rev y x] at hy
  dsimp [sourcePayoff]
  linarith [hfg y]

/-- The name "least Lipschitz majorant" is justified by a proved universal property. -/
theorem majorant_eq_of_lipschitz {f : E → ℝ} {L : ℝ}
    (hfinite : MajorantFinite f L) (hf : GloballyLipschitz L f) :
    lipschitzMajorant f L = f := by
  funext x
  exact le_antisymm (majorant_le_of_lipschitz_majorizes hf (fun _ => le_rfl) x)
    (le_lipschitzMajorant hfinite x)

theorem majorant_bounded_below {f : E → ℝ} {L m : ℝ}
    (hfinite : MajorantFinite f L) (hm : ∀ x, m ≤ f x) (x : E) :
    m ≤ lipschitzMajorant f L x :=
  (hm x).trans (le_lipschitzMajorant hfinite x)

theorem source_radius_bound {f : E → ℝ} {L c A : ℝ}
    (hfinite : MajorantFinite f L) {x y : E}
    (hsource : sourcePayoff f L x y = lipschitzMajorant f L x)
    (hgrowth : f y - f x ≤ c * ‖x - y‖ + A) :
    (L - c) * ‖x - y‖ ≤ A := by
  have hx := le_lipschitzMajorant hfinite x
  rw [← hsource] at hx
  dsimp [sourcePayoff] at hx
  nlinarith

/-- Every attained source is a contact point: `F(y) = f(y)`. -/
theorem majorant_source_contact {f : E → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hfinite : MajorantFinite f L) {x y : E}
    (hsource : sourcePayoff f L x y = lipschitzMajorant f L x) :
    lipschitzMajorant f L y = f y := by
  apply le_antisymm
  · have h := majorant_sub_le hL hfinite y x
    rw [norm_sub_rev y x, ← hsource] at h
    dsimp [sourcePayoff] at h
    linarith
  · exact le_lipschitzMajorant hfinite y

end WC
