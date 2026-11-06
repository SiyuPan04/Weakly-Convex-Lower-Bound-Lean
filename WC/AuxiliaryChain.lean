import WC.BoundaryLower
import WC.BinaryMaximumRule
import WC.ParametricOracle

/-! The actual single convex tilted chain used in the bounded-gap-ratio regime. -/

noncomputable section
namespace WC
namespace BoundaryLower

open scoped BigOperators

inductive AuxiliaryFacet (K : ℕ) where
  | zero
  | coordinate (i : Fin K)
  deriving DecidableEq, Fintype

instance (K : ℕ) : Inhabited (AuxiliaryFacet K) := ⟨AuxiliaryFacet.zero⟩
instance (K : ℕ) : MetricSpace (AuxiliaryFacet K) :=
  MetricSpace.induced (fun a => (((Fintype.equivFin (AuxiliaryFacet K)) a).val : ℝ)) (by
    intro a b h
    apply (Fintype.equivFin (AuxiliaryFacet K)).injective
    apply Fin.ext
    exact Nat.cast_injective h) inferInstance
instance (K : ℕ) : DiscreteTopology (AuxiliaryFacet K) := by infer_instance
instance (K : ℕ) : CompactSpace (AuxiliaryFacet K) := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : ℕ}

def auxiliaryFacet (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) : AuxiliaryFacet K → E → ℝ
  | .zero, _ => 0
  | .coordinate i, x => a i - A * inner ℝ (u i) x

def auxiliaryFan (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) : E → ℝ :=
  compactMaximum (auxiliaryFacet A a u)

theorem auxiliaryFacet_continuous (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) :
    Continuous (fun p : AuxiliaryFacet K × E => auxiliaryFacet A a u p.1 p.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro k
  cases k
  · exact continuous_const
  · exact continuous_const.sub (continuous_const.mul (continuous_const.inner continuous_id))

theorem auxiliaryFacet_convex (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) (k : AuxiliaryFacet K) :
    ConvexOn ℝ Set.univ (auxiliaryFacet A a u k) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t _ _ hst
  cases k with
  | zero => simp [auxiliaryFacet]
  | coordinate i =>
    have hc : (s + t) * a i = a i := by rw [hst, one_mul]
    simp only [auxiliaryFacet, inner_add_right, real_inner_smul_right, smul_eq_mul]
    nlinarith

theorem convex_weaklyConvex {ρ : ℝ} {f : E → ℝ} (hρ : 0 ≤ ρ) (hf : ConvexOn ℝ Set.univ f) :
    WeaklyConvex ρ f := by
  have hnorm : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  exact hf.add (hnorm.smul (show 0 ≤ ρ / 2 by positivity))

theorem auxiliaryFan_convex (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) :
    ConvexOn ℝ Set.univ (auxiliaryFan A a u) := by
  have h := compactMaximum_weaklyConvex (ρ := 0) (auxiliaryFacet_continuous A a u)
    (fun k => convex_weaklyConvex le_rfl (auxiliaryFacet_convex A a u k))
  simpa only [WeaklyConvex, auxiliaryFan, zero_div, zero_mul, add_zero] using h

theorem auxiliaryFacet_lipschitz {A : ℝ} (hA : 0 ≤ A) (a : Fin K → ℝ)
    {u : Fin K → E} (hu : Orthonormal ℝ u) (k : AuxiliaryFacet K) :
    GloballyLipschitz A (auxiliaryFacet A a u k) := by
  intro x y
  cases k with
  | zero => simp only [auxiliaryFacet, sub_self, abs_zero]; positivity
  | coordinate i =>
    have hinner := abs_real_inner_le_norm (u i) (x - y)
    rw [hu.norm_eq_one, one_mul] at hinner
    have hid : (a i - A * inner ℝ (u i) x) - (a i - A * inner ℝ (u i) y) =
        -A * inner ℝ (u i) (x - y) := by rw [inner_sub_right]; ring
    change |(a i - A * inner ℝ (u i) x) - (a i - A * inner ℝ (u i) y)| ≤ _
    rw [hid, abs_mul, abs_neg, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hinner hA

theorem auxiliaryFan_lipschitz {A : ℝ} (hA : 0 ≤ A) (a : Fin K → ℝ)
    {u : Fin K → E} (hu : Orthonormal ℝ u) : GloballyLipschitz A (auxiliaryFan A a u) :=
  compactMaximum_lipschitz (auxiliaryFacet_continuous A a u) (auxiliaryFacet_lipschitz hA a hu)

theorem auxiliaryFan_nonneg (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) (x : E) :
    0 ≤ auxiliaryFan A a u x := branch_le_compactMaximum (auxiliaryFacet_continuous A a u) .zero x

theorem auxiliary_piece_le (A : ℝ) (a : Fin K → ℝ) (u : Fin K → E) (x : E) (i : Fin K) :
    a i - A * inner ℝ (u i) x ≤ auxiliaryFan A a u x :=
  branch_le_compactMaximum (auxiliaryFacet_continuous A a u) (.coordinate i) x

theorem auxiliaryFan_le {A c : ℝ} {a : Fin K → ℝ} {u : Fin K → E} {x : E}
    (hc : 0 ≤ c) (hpiece : ∀ i, a i - A * inner ℝ (u i) x ≤ c) : auxiliaryFan A a u x ≤ c := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k, rfl⟩
  cases k
  · exact hc
  · exact hpiece _

theorem auxiliaryFan_origin_le {A a₀ : ℝ} {a : Fin K → ℝ} (u : Fin K → E)
    (ha₀ : 0 ≤ a₀) (ha : ∀ i, a i ≤ a₀) : auxiliaryFan A a u 0 ≤ a₀ := by
  apply auxiliaryFan_le ha₀
  intro i
  simpa using ha i

def fanDirection (u : Fin K → E) : E := ∑ i, u i

theorem inner_fanDirection {u : Fin K → E} (hu : Orthonormal ℝ u) (i : Fin K) :
    inner ℝ (u i) (fanDirection u) = 1 := by
  simpa only [fanDirection, one_smul] using hu.inner_right_fintype (fun _ => (1 : ℝ)) i

theorem fanDirection_norm_sq {u : Fin K → E} (hu : Orthonormal ℝ u) :
    ‖fanDirection u‖ ^ 2 = K := by
  rw [← real_inner_self_eq_norm_sq]
  unfold fanDirection
  rw [sum_inner]
  simp only [show ∀ i : Fin K, inner ℝ (u i) (∑ j, u j) = 1 from inner_fanDirection hu,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- A short uniform shift of all frame coordinates lowers every positive fan branch. -/
theorem auxiliaryFan_shift_le {A t : ℝ} {a : Fin K → ℝ} {u : Fin K → E}
    (hu : Orthonormal ℝ u) (x : E) (ht : A * t ≤ auxiliaryFan A a u x) :
    auxiliaryFan A a u (x + t • fanDirection u) ≤ auxiliaryFan A a u x - A * t := by
  apply auxiliaryFan_le (by linarith)
  intro i
  have hpiece := auxiliary_piece_le A a u x i
  rw [inner_add_right, real_inner_smul_right, inner_fanDirection hu, mul_one]
  linarith

/-- Every genuine subgradient on a positive fan level has a large component along the diagonal. -/
theorem auxiliaryFan_subgradient_diagonal [CompleteSpace E] {A : ℝ} (hA : 0 < A)
    {a : Fin K → ℝ} {u : Fin K → E} (hu : Orthonormal ℝ u) {x v : E}
    (hpos : 0 < auxiliaryFan A a u x) (hv : FrechetSubgradient (auxiliaryFan A a u) x v) :
    inner ℝ v (fanDirection u) ≤ -A := by
  have hsupport := (weakSubgradient_iff_frechet (ρ := 0) le_rfl
    (convex_weaklyConvex le_rfl (auxiliaryFan_convex A a u))).mpr hv
  let t := auxiliaryFan A a u x / (2 * A)
  have ht : 0 < t := div_pos hpos (by positivity)
  have hAt : A * t = auxiliaryFan A a u x / 2 := by dsimp [t]; field_simp
  have hupper := auxiliaryFan_shift_le hu x (by rw [hAt]; linarith : A * t ≤ auxiliaryFan A a u x)
  have hlower := hsupport (x + t • fanDirection u)
  simp only [add_sub_cancel_left, real_inner_smul_right, zero_div, zero_mul, sub_zero] at hlower
  nlinarith

theorem auxiliaryFan_subgradient_inner_lower [CompleteSpace E] {A a₀ : ℝ}
    {a : Fin K → ℝ} {u : Fin K → E} (ha₀ : 0 ≤ a₀) (ha : ∀ i, a i ≤ a₀) {x v : E}
    (hv : FrechetSubgradient (auxiliaryFan A a u) x v) : -a₀ ≤ inner ℝ v x := by
  have hsupport := (weakSubgradient_iff_frechet (ρ := 0) le_rfl
    (convex_weaklyConvex le_rfl (auxiliaryFan_convex A a u))).mpr hv
  have hzero := hsupport 0
  simp only [zero_sub, inner_neg_right, zero_div, zero_mul, sub_zero] at hzero
  linarith [auxiliaryFan_origin_le (A := A) u ha₀ ha, auxiliaryFan_nonneg A a u x]

theorem auxiliaryFan_subgradient_norm_sq [CompleteSpace E] {A : ℝ} (hA : 0 < A)
    {a : Fin K → ℝ} {u : Fin K → E} (hu : Orthonormal ℝ u) {x v : E}
    (hpos : 0 < auxiliaryFan A a u x) (hv : FrechetSubgradient (auxiliaryFan A a u) x v) :
    A ^ 2 ≤ (K : ℝ) * ‖v‖ ^ 2 := by
  have hdiag := auxiliaryFan_subgradient_diagonal hA hu hpos hv
  have hc := abs_real_inner_le_norm v (fanDirection u)
  have habs : A ≤ |inner ℝ v (fanDirection u)| := by
    have := neg_le_abs (inner ℝ v (fanDirection u))
    linarith
  have hprod : A ≤ ‖v‖ * ‖fanDirection u‖ := habs.trans hc
  have hsq := (sq_le_sq₀ hA.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hprod
  rw [mul_pow, fanDirection_norm_sq hu] at hsq
  nlinarith

end BoundaryLower
end WC
