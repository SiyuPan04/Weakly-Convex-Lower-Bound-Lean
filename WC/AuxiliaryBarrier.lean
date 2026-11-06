import WC.AuxiliaryChain
import WC.RadialExterior

/-! The actual convex auxiliary chain with a radial wall and its Moreau barrier. -/

noncomputable section
namespace WC
namespace BoundaryLower

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : ℕ}

def auxiliaryRadial (G a₀ R : ℝ) (x : E) : ℝ := a₀ + G * (‖x‖ - R)

def auxiliaryChain (G A a₀ R : ℝ) (a : Fin K → ℝ) (u : Fin K → E) (x : E) : ℝ :=
  max (auxiliaryFan A a u x) (auxiliaryRadial G a₀ R x)

theorem auxiliaryRadial_convex {G : ℝ} (hG : 0 ≤ G) (a₀ R : ℝ) :
    ConvexOn ℝ Set.univ (auxiliaryRadial G a₀ R : E → ℝ) := by
  apply ((convexOn_univ_norm.smul hG).add_const (a₀ - G * R)).congr
  intro x _
  dsimp [auxiliaryRadial]
  ring

omit [InnerProductSpace ℝ E] in
theorem auxiliaryRadial_lipschitz {G : ℝ} (hG : 0 ≤ G) (a₀ R : ℝ) :
    GloballyLipschitz G (auxiliaryRadial G a₀ R : E → ℝ) := by
  intro x y
  have h := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) hG
  have hid : auxiliaryRadial G a₀ R x - auxiliaryRadial G a₀ R y = G * (‖x‖ - ‖y‖) := by
    dsimp [auxiliaryRadial]; ring
  simpa only [hid, abs_mul, abs_of_nonneg hG] using h

theorem auxiliaryChain_convex {G : ℝ} (hG : 0 ≤ G) (A a₀ R : ℝ)
    (a : Fin K → ℝ) (u : Fin K → E) :
    ConvexOn ℝ Set.univ (auxiliaryChain G A a₀ R a u) :=
  (auxiliaryFan_convex A a u).sup (auxiliaryRadial_convex hG a₀ R)

theorem auxiliaryChain_lipschitz {G A a₀ R : ℝ} (hA : 0 ≤ A) (hAG : A ≤ G)
    (a : Fin K → ℝ) {u : Fin K → E} (hu : Orthonormal ℝ u) :
    GloballyLipschitz G (auxiliaryChain G A a₀ R a u) :=
  ((auxiliaryFan_lipschitz hA a hu).mono hAG).max
    (auxiliaryRadial_lipschitz (hA.trans hAG) a₀ R)

theorem auxiliaryChain_gap {G A a₀ R : ℝ} (hG : 0 ≤ G) (ha₀ : 0 ≤ a₀) (hR : 0 ≤ R)
    {a : Fin K → ℝ} (ha : ∀ i, a i ≤ a₀) (u : Fin K → E) :
    GapBound a₀ (auxiliaryChain G A a₀ R a u) := by
  intro x
  have h0 : auxiliaryChain G A a₀ R a u 0 ≤ a₀ := by
    apply max_le (auxiliaryFan_origin_le u ha₀ ha)
    dsimp [auxiliaryRadial]
    simp only [norm_zero]
    nlinarith
  have hx : 0 ≤ auxiliaryChain G A a₀ R a u x :=
    (auxiliaryFan_nonneg A a u x).trans (le_max_left _ _)
  linarith

theorem auxiliaryChain_admissible {G A a₀ R ρ : ℝ} (hA : 0 ≤ A) (hAG : A ≤ G)
    (hρ : 0 ≤ ρ) (ha₀ : 0 ≤ a₀) (hR : 0 ≤ R) {a : Fin K → ℝ}
    (ha : ∀ i, a i ≤ a₀) {u : Fin K → E} (hu : Orthonormal ℝ u) :
    Admissible G ρ a₀ (auxiliaryChain G A a₀ R a u) :=
  ⟨convex_weaklyConvex hρ (auxiliaryChain_convex (hA.trans hAG) A a₀ R a u),
    auxiliaryChain_lipschitz hA hAG a hu, auxiliaryChain_gap (hA.trans hAG) ha₀ hR ha u⟩

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem auxiliaryFan_zero_displacement {A aMin η : ℝ} (hA : 0 < A)
    {a : Fin K → ℝ} {u : Fin K → E} (hu : Orthonormal ℝ u) {x p : E}
    (s : Finset (Fin K)) (ha : ∀ i ∈ s, aMin ≤ a i)
    (hsmall : ∀ i ∈ s, |inner ℝ (u i) x| ≤ η)
    (hmargin : 0 ≤ aMin / A - η) (hzero : auxiliaryFan A a u p = 0) :
    (s.card : ℝ) * (aMin / A - η) ^ 2 ≤ ‖p - x‖ ^ 2 := by
  have hcoord (i : Fin K) (hi : i ∈ s) : aMin / A - η ≤ inner ℝ (u i) (p - x) := by
    have hp := auxiliary_piece_le A a u p i
    rw [hzero] at hp
    have hx := (le_abs_self (inner ℝ (u i) x)).trans (hsmall i hi)
    have hdiv : aMin / A ≤ inner ℝ (u i) p := (div_le_iff₀ hA).mpr (by linarith [ha i hi])
    rw [inner_sub_right]
    linarith
  have hsum : ∑ i ∈ s, (aMin / A - η) ^ 2 ≤ ∑ i ∈ s, ‖inner ℝ (u i) (p - x)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h := hcoord i hi
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith
  simpa only [Finset.sum_const, nsmul_eq_mul] using hsum.trans (hu.sum_inner_products_le (p - x))

omit [CompleteSpace E] in
/-- A quantitative radial tie cannot cancel a positive fan subgradient. -/
theorem auxiliary_vector_margin {ε G w : ℝ} {h e : E}
    (hε : 0 < ε) (hG : 0 < G) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (he : ‖e‖ = 1)
    (hh : 2 * ε ^ 2 ≤ ‖h‖ ^ 2) (hGlarge : 4 * ε ^ 2 ≤ G ^ 2)
    (hinner : -(ε ^ 2) / (3 * G) ≤ inner ℝ h e) :
    ε ^ 2 < ‖w • h + (G * (1 - w)) • e‖ ^ 2 := by
  have hq : 0 ≤ G * (1 - w) := by positivity
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hw0, abs_of_nonneg hq, he, mul_one,
    real_inner_smul_left, real_inner_smul_right]
  have h1 := mul_le_mul_of_nonneg_left hh (sq_nonneg w)
  have h2 := mul_le_mul_of_nonneg_left hGlarge (sq_nonneg (1 - w))
  have hi : -(ε ^ 2) ≤ 3 * G * inner ℝ h e := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 3 * G)).mp hinner
  have h3 := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * w * (1 - w) by positivity)
  have h4 := mul_nonneg (sq_nonneg (2 * w - 1)) (sq_nonneg ε)
  have h5 := mul_nonneg (sq_nonneg (3 * w - 2)) (sq_nonneg ε)
  nlinarith [sq_pos_of_pos hε]

theorem auxiliaryRadial_hasGradientAt {G a₀ R : ℝ} {x : E} (hx : x ≠ 0) :
    HasGradientAt (auxiliaryRadial G a₀ R) ((G / ‖x‖) • x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (((hasGradientAt_norm_of_ne_zero hx).hasFDerivAt.sub_const R).const_mul G).const_add a₀
  convert! h using 1
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply, real_inner_smul_left, smul_eq_mul]
  ring

variable [ProperSpace E] [FiniteDimensional ℝ E]

/-- This decomposition uses the full actual subdifferential of the maximum, including ties. -/
theorem auxiliaryChain_subgradient_cases {G A a₀ R : ℝ} (hA : 0 ≤ A) (hAG : A ≤ G)
    (a : Fin K → ℝ) {u : Fin K → E} (hu : Orthonormal ℝ u) {x v : E}
    (hactive_ne : auxiliaryFan A a u x ≤ auxiliaryRadial G a₀ R x → x ≠ 0)
    (hv : v ∈ subdifferential (auxiliaryChain G A a₀ R a u) x) :
    v ∈ subdifferential (auxiliaryFan A a u) x ∨
      ∃ (w : ℝ) (h : E), 0 ≤ w ∧ w ≤ 1 ∧ h ∈ subdifferential (auxiliaryFan A a u) x ∧
        auxiliaryFan A a u x ≤ auxiliaryRadial G a₀ R x ∧ x ≠ 0 ∧
        v = w • h + (1 - w) • ((G / ‖x‖) • x) := by
  have hG := hA.trans hAG
  have hfLip := (auxiliaryFan_lipschitz hA a hu).mono hAG
  have hgLip := auxiliaryRadial_lipschitz (E := E) hG a₀ R
  have hfWC := convex_weaklyConvex (ρ := 0) le_rfl (auxiliaryFan_convex A a u)
  have hgWC := convex_weaklyConvex (ρ := 0) le_rfl (auxiliaryRadial_convex (E := E) hG a₀ R)
  by_cases hh : auxiliaryRadial G a₀ R x < auxiliaryFan A a u x
  · exact Or.inl ((subdifferential_max_left_of_lt hG le_rfl hfLip hgLip hfWC hgWC hh) ▸ hv)
  have hactive := le_of_not_gt hh
  have hx := hactive_ne hactive
  have hrad : subdifferential (auxiliaryRadial G a₀ R) x = {(G / ‖x‖) • x} := by
    ext g
    exact frechetSubgradient_iff_gradient (auxiliaryRadial_hasGradientAt hx)
  have hmax : v ∈ convexHull ℝ (binaryActiveSlopes (auxiliaryFan A a u) (auxiliaryRadial G a₀ R) x) := by
    change v ∈ subdifferential (fun y => max (auxiliaryFan A a u y) (auxiliaryRadial G a₀ R y)) x at hv
    rwa [subdifferential_max_eq_convexHull hG le_rfl hfLip hgLip hfWC hgWC] at hv
  have hsub : binaryActiveSlopes (auxiliaryFan A a u) (auxiliaryRadial G a₀ R) x ⊆
      subdifferential (auxiliaryFan A a u) x ∪ {(G / ‖x‖) • x} := by
    intro g hg
    rcases hg with ⟨_, hg⟩ | ⟨_, hg⟩
    · exact Or.inl hg
    · exact Or.inr (hrad ▸ hg)
  obtain ⟨w, h, hw0, hw1, hmem, heq⟩ := convexHull_union_singleton_representation
    (subdifferential_convex x le_rfl hfWC) (subdifferential_nonempty x hA le_rfl
      (auxiliaryFan_lipschitz hA a hu) hfWC) ((G / ‖x‖) • x) (convexHull_mono hsub hmax)
  exact Or.inr ⟨w, h, hw0, hw1, hmem, hactive, hx, heq⟩

/-- The auxiliary lower bound is for the gradient of the actual Moreau envelope. -/
theorem auxiliaryChain_moreau_barrier {G A R ρ ε aMin η : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hA : 0 < A) (hAG : A ≤ G) (hK : 0 < K)
    (hAlarge : 2 * (K : ℝ) * ε ^ 2 ≤ A ^ 2) (hGlarge : 4 * ε ^ 2 ≤ G ^ 2)
    (hR : 3 * G / ρ + (ε ^ 2 / ρ) / G ≤ R)
    {a : Fin K → ℝ} (ha : ∀ i, a i ≤ ε ^ 2 / ρ)
    {u : Fin K → E} (hu : Orthonormal ℝ u) (s : Finset (Fin K))
    (hamin : ∀ i ∈ s, aMin ≤ a i) (hmargin : 0 ≤ aMin / A - η)
    (hbudget : ε ^ 2 / (4 * ρ ^ 2) < (s.card : ℝ) * (aMin / A - η) ^ 2)
    (x : E) (hsmall : ∀ i ∈ s, |inner ℝ (u i) x| ≤ η) :
    ε < ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (auxiliaryChain G A (ε ^ 2 / ρ) R a u)) x‖ := by
  have hG : 0 < G := hA.trans_le hAG
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  let H := auxiliaryChain G A (ε ^ 2 / ρ) R a u
  let p := proximalPoint ρ H x
  let v := (2 * ρ) • (x - p)
  have hLip : GloballyLipschitz G H := auxiliaryChain_lipschitz hA.le hAG a hu
  have hWC : WeaklyConvex ρ H := convex_weaklyConvex hρ.le
    (auxiliaryChain_convex hG.le A (ε ^ 2 / ρ) R a u)
  have hp := proximalPoint_spec hρ hG.le hLip x
  have hv : v ∈ subdifferential H p := (hp.weakSubgradient hρ hWC).frechet hρ.le
  have hg : gradient (moreauEnvelope (1 / (2 * ρ)) H) x = v :=
    moreau_gradient_eq hρ hG.le hLip hWC x
  rw [hg]
  by_contra hfail
  have hvsmall : ‖v‖ ≤ ε := le_of_not_gt hfail
  have hvsq : ‖v‖ ^ 2 ≤ ε ^ 2 := (sq_le_sq₀ (norm_nonneg v) hε.le).mpr hvsmall
  have hvnorm : ‖v‖ = 2 * ρ * ‖x - p‖ := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity)]
  have hdist : ‖p - x‖ ^ 2 ≤ ε ^ 2 / (4 * ρ ^ 2) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * ρ ^ 2), norm_sub_rev]
    rw [hvnorm] at hvsq
    nlinarith only [hvsq]
  have hpos : 0 < auxiliaryFan A a u p := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (auxiliaryFan_nonneg A a u p)
    have hb := auxiliaryFan_zero_displacement hA hu s hamin hsmall hmargin hz
    linarith
  have hfan (h : E) (hh : h ∈ subdifferential (auxiliaryFan A a u) p) :
      2 * ε ^ 2 ≤ ‖h‖ ^ 2 := by
    have hn := auxiliaryFan_subgradient_norm_sq hA hu hpos hh
    nlinarith
  have hactive_bound (hh : auxiliaryFan A a u p ≤ auxiliaryRadial G (ε ^ 2 / ρ) R p) :
      3 * G / ρ ≤ ‖p‖ := by
    have hn := auxiliaryFan_nonneg A a u p
    have hdiv : R - (ε ^ 2 / ρ) / G ≤ ‖p‖ := by
      apply (le_of_mul_le_mul_left ?_ hG)
      dsimp [auxiliaryRadial] at hh
      rw [mul_sub, mul_div_cancel₀ _ hG.ne']
      nlinarith
    linarith
  have hactive_ne (hh : auxiliaryFan A a u p ≤ auxiliaryRadial G (ε ^ 2 / ρ) R p) : p ≠ 0 :=
    norm_pos_iff.mp ((div_pos (by positivity) hρ).trans_le (hactive_bound hh))
  rcases auxiliaryChain_subgradient_cases hA.le hAG a hu hactive_ne hv with hh |
      ⟨w, h, hw0, hw1, hh, hactive, hpne, hrep⟩
  · have hn := hfan v hh
    nlinarith [sq_pos_of_pos hε]
  · have hr : 0 < ‖p‖ := norm_pos_iff.mpr hpne
    have hinner := auxiliaryFan_subgradient_inner_lower (A := A) (u := u)
      (by positivity : 0 ≤ ε ^ 2 / ρ) ha hh
    have hratio : (ε ^ 2 / ρ) / ‖p‖ ≤ ε ^ 2 / (3 * G) := by
      apply (div_le_div_iff₀ hr (by positivity : 0 < 3 * G)).mpr
      have hb := mul_le_mul_of_nonneg_left (hactive_bound hactive) (sq_nonneg ε)
      convert hb using 1
      field_simp
    have hi : -(ε ^ 2) / (3 * G) ≤ inner ℝ h (‖p‖⁻¹ • p) := by
      rw [real_inner_smul_right]
      have hm := mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hr.le)
      have heq : ‖p‖⁻¹ * (-(ε ^ 2 / ρ)) = -((ε ^ 2 / ρ) / ‖p‖) := by ring
      rw [heq] at hm
      have hn : -(ε ^ 2) / (3 * G) ≤ -((ε ^ 2 / ρ) / ‖p‖) := by
        simpa only [neg_div] using neg_le_neg hratio
      exact hn.trans hm
    have he : ‖‖p‖⁻¹ • p‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hb := auxiliary_vector_margin hε hG hw0 hw1 he (hfan h hh) hGlarge hi
    have hvec : (1 - w) • ((G / ‖p‖) • p) = (G * (1 - w)) • (‖p‖⁻¹ • p) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [hvec] at hrep
    rw [← hrep] at hb
    nlinarith

end BoundaryLower
end WC
