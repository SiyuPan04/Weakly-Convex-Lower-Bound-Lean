import WC.AuxiliaryNormalized
import Mathlib.Topology.Order.Lattice

/-! Exact complete-oracle locality and globally defined Borel prefix responses
for the auxiliary convex fan. -/

noncomputable section
namespace WC
namespace BoundaryLower

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : ℕ}

def maskedIntercept (ε : ℝ) (K t : ℕ) (i : Fin K) : ℝ :=
  if i.val ≤ t then auxiliaryIntercept ε K i else 0

def maskedFrame (t : ℕ) (u : Fin K → E) (i : Fin K) : E :=
  if i.val ≤ t then u i else 0

def truncatedAuxiliary (ε : ℝ) (t : ℕ) (u : Fin K → E) : E → ℝ :=
  auxiliaryChain 1 (1 / 2) (ε ^ 2) 4 (maskedIntercept ε K t) (maskedFrame t u)

theorem auxiliary_intercept_gap {ε : ℝ} {i j : Fin K} (hij : i.val < j.val) :
    ε ^ 2 / (16 * K) ≤ auxiliaryIntercept ε K i - auxiliaryIntercept ε K j := by
  have hK : 0 < K := Nat.zero_lt_of_lt j.isLt
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  unfold auxiliaryIntercept
  apply (le_of_mul_le_mul_right ?_ (by positivity : 0 < 16 * (K : ℝ)))
  field_simp
  nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hd)]

theorem auxiliaryFan_mask_le (ε : ℝ) (t : ℕ) (u : Fin K → E) (x : E) :
    auxiliaryFan (1 / 2) (maskedIntercept ε K t) (maskedFrame t u) x ≤
      auxiliaryFan (1 / 2) (auxiliaryIntercept ε K) u x := by
  apply auxiliaryFan_le (auxiliaryFan_nonneg _ _ _ _)
  intro i
  by_cases hi : i.val ≤ t
  · simpa only [maskedIntercept, maskedFrame, if_pos hi] using
      auxiliary_piece_le (1 / 2) (auxiliaryIntercept ε K) u x i
  · simpa only [maskedIntercept, maskedFrame, if_neg hi, inner_zero_left, mul_zero, sub_zero] using
      auxiliaryFan_nonneg (1 / 2) (auxiliaryIntercept ε K) u x

theorem auxiliaryFan_eq_mask {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : t < K)
    (u : Fin K → E) (x : E)
    (hsmall : ∀ i : Fin K, t ≤ i.val → |inner ℝ (u i) x| < auxiliaryEta ε K) :
    auxiliaryFan (1 / 2) (auxiliaryIntercept ε K) u x =
      auxiliaryFan (1 / 2) (maskedIntercept ε K t) (maskedFrame t u) x := by
  apply le_antisymm ?_ (auxiliaryFan_mask_le ε t u x)
  apply auxiliaryFan_le (auxiliaryFan_nonneg _ _ _ _)
  intro j
  by_cases hj : j.val ≤ t
  · simpa only [maskedIntercept, maskedFrame, if_pos hj] using
      auxiliary_piece_le (1 / 2) (maskedIntercept ε K t) (maskedFrame t u) x j
  · let i : Fin K := ⟨t, ht⟩
    have hi : i.val ≤ t := le_refl _
    have hgap := auxiliary_intercept_gap (ε := ε) (i := i) (j := j) (by omega)
    have hismall := (abs_lt.mp (hsmall i (by rfl))).2
    have hjsmall := (abs_lt.mp (hsmall j (by omega))).1
    have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.zero_lt_of_lt ht
    have hη : 0 < auxiliaryEta ε K := div_pos (sq_pos_of_pos hε) (by positivity)
    have hid : ε ^ 2 / (16 * K) = 2 * auxiliaryEta ε K := by unfold auxiliaryEta; ring
    rw [hid] at hgap
    have hbranch : auxiliaryIntercept ε K j - (1 / 2) * inner ℝ (u j) x ≤
        auxiliaryIntercept ε K i - (1 / 2) * inner ℝ (u i) x := by linarith
    have hretained : auxiliaryIntercept ε K i - (1 / 2) * inner ℝ (u i) x ≤
        auxiliaryFan (1 / 2) (maskedIntercept ε K t) (maskedFrame t u) x := by
      simpa only [maskedIntercept, maskedFrame, if_pos hi] using
        auxiliary_piece_le (1 / 2) (maskedIntercept ε K t) (maskedFrame t u) x i
    exact hbranch.trans hretained

theorem normalizedAuxiliary_eventuallyEq_truncated {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : t < auxiliaryLength ε) (u : Fin (auxiliaryLength ε) → E) (x : E)
    (hsmall : ∀ i : Fin (auxiliaryLength ε), t ≤ i.val →
      |inner ℝ (u i) x| < auxiliaryEta ε (auxiliaryLength ε)) :
    normalizedAuxiliary ε u =ᶠ[𝓝 x] truncatedAuxiliary ε t u := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i : Fin (auxiliaryLength ε), t ≤ i.val →
      |inner ℝ (u i) y| < auxiliaryEta ε (auxiliaryLength ε) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : t ≤ i.val
    · have hcont : Continuous (fun y : E => |inner ℝ (u i) y|) :=
        (continuous_const.inner continuous_id).abs
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds (hsmall i hi))] with y hy
      exact fun _ => hy
    · exact Filter.Eventually.of_forall (fun _ hh => (hi hh).elim)
  filter_upwards [hnear] with y hy
  exact congrArg (fun z => max z (auxiliaryRadial 1 (ε ^ 2) 4 y)) (auxiliaryFan_eq_mask hε ht u y hy)

theorem normalizedAuxiliary_oracle_locality [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : t < auxiliaryLength ε)
    (u : Fin (auxiliaryLength ε) → E) (x : E)
    (hsmall : ∀ i : Fin (auxiliaryLength ε), t ≤ i.val →
      |inner ℝ (u i) x| < auxiliaryEta ε (auxiliaryLength ε)) :
    normalizedAuxiliary ε u x = truncatedAuxiliary ε t u x ∧
      subdifferential (normalizedAuxiliary ε u) x = subdifferential (truncatedAuxiliary ε t u) x := by
  have heq := normalizedAuxiliary_eventuallyEq_truncated hε ht u x hsmall
  refine ⟨heq.eq_of_nhds, Set.ext fun v => ?_⟩
  exact frechetSubgradient_congr_eventuallyEq heq

theorem auxiliaryFan_lipschitz_bound {A : ℝ} (hA : 0 ≤ A) (a : Fin K → ℝ)
    {u : Fin K → E} (hu : ∀ i, ‖u i‖ ≤ 1) : GloballyLipschitz A (auxiliaryFan A a u) := by
  apply compactMaximum_lipschitz (auxiliaryFacet_continuous A a u)
  intro k x y
  cases k with
  | zero => simp only [auxiliaryFacet, sub_self, abs_zero]; positivity
  | coordinate i =>
    have hi := (abs_real_inner_le_norm (u i) (x - y)).trans
      (mul_le_mul_of_nonneg_right (hu i) (norm_nonneg (x - y)))
    rw [one_mul] at hi
    have hid : (a i - A * inner ℝ (u i) x) - (a i - A * inner ℝ (u i) y) =
        -A * inner ℝ (u i) (x - y) := by rw [inner_sub_right]; ring
    change |(a i - A * inner ℝ (u i) x) - (a i - A * inner ℝ (u i) y)| ≤ _
    rw [hid, abs_mul, abs_neg, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hi hA

theorem truncatedAuxiliary_weaklyConvex (ε : ℝ) (t : ℕ) (u : Fin K → E) :
    WeaklyConvex 1 (truncatedAuxiliary ε t u) :=
  convex_weaklyConvex (by norm_num) (auxiliaryChain_convex (by norm_num) _ _ _ _ _)

theorem truncatedAuxiliary_lipschitz (ε : ℝ) (t : ℕ) {u : Fin K → E}
    (hu : ∀ i, ‖u i‖ ≤ 1) : GloballyLipschitz 1 (truncatedAuxiliary ε t u) := by
  have hm : ∀ i, ‖maskedFrame t u i‖ ≤ 1 := by
    intro i
    by_cases hi : i.val ≤ t
    · simpa only [maskedFrame, if_pos hi] using hu i
    · simp only [maskedFrame, if_neg hi, norm_zero, zero_le_one]
  exact ((auxiliaryFan_lipschitz_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (maskedIntercept ε K t) hm).mono (by norm_num)).max
    (auxiliaryRadial_lipschitz (by norm_num) (ε ^ 2) 4)

theorem finiteMaximum_continuous {D ι : Type*} [TopologicalSpace D] [Fintype ι] [Nonempty ι]
    (f : ι → D → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => sSup (Set.range (fun i => f i x))) := by
  change Continuous (fun x => ⨆ i, f i x)
  simp_rw [← Finset.sup'_univ_eq_ciSup]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => hf i)

theorem truncatedAuxiliary_joint_continuous (ε : ℝ) (t : ℕ) :
    Continuous (fun p : (Fin K → E) × E => truncatedAuxiliary ε t p.1 p.2) := by
  apply Continuous.max ?_ (continuous_const.add (continuous_const.mul (continuous_snd.norm.sub continuous_const)))
  apply finiteMaximum_continuous
  intro k
  cases k with
  | zero => exact continuous_const
  | coordinate i =>
    by_cases hi : i.val ≤ t
    · change Continuous (fun p : (Fin K → E) × E =>
        maskedIntercept ε K t i - (1 / 2) * inner ℝ (maskedFrame t p.1 i) p.2)
      simp only [maskedFrame, if_pos hi]
      exact continuous_const.sub (continuous_const.mul
        (((continuous_apply i).comp continuous_fst).inner continuous_snd))
    · change Continuous (fun p : (Fin K → E) × E =>
        maskedIntercept ε K t i - (1 / 2) * inner ℝ (maskedFrame t p.1 i) p.2)
      simpa only [maskedFrame, if_neg hi, inner_zero_left, mul_zero, sub_zero] using
        (continuous_const : Continuous (fun _ : (Fin K → E) × E => maskedIntercept ε K t i))

abbrev AuxiliaryBoundedFrame (K : ℕ) (E : Type*) [NormedAddCommGroup E] :=
  {u : Fin K → E // ∀ i, ‖u i‖ ≤ 1}

theorem normalizedAuxiliary_joint_continuous (ε : ℝ) :
    Continuous (fun p : (Fin (auxiliaryLength ε) → E) × E => normalizedAuxiliary ε p.1 p.2) := by
  apply Continuous.max ?_ (continuous_const.add (continuous_const.mul (continuous_snd.norm.sub continuous_const)))
  apply finiteMaximum_continuous
  intro k
  cases k with
  | zero => exact continuous_const
  | coordinate i => exact continuous_const.sub (continuous_const.mul
      (((continuous_apply i).comp continuous_fst).inner continuous_snd))

variable [CompleteSpace E] [ProperSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

def auxiliaryPrefixOracle (ε : ℝ) (t : ℕ) (u : AuxiliaryBoundedFrame K E) (x : E) :
    ℝ × CompactConvexSets E :=
  fullOracle (by norm_num) (by norm_num) (truncatedAuxiliary_lipschitz ε t u.property)
    (truncatedAuxiliary_weaklyConvex ε t u.val) x

theorem auxiliaryPrefixOracle_measurable (ε : ℝ) (t : ℕ) :
    Measurable (fun p : AuxiliaryBoundedFrame K E × E => auxiliaryPrefixOracle ε t p.1 p.2) := by
  apply parameterized_fullOracle_measurable (by norm_num) (by norm_num)
  · exact (truncatedAuxiliary_joint_continuous ε t).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

omit [CompleteSpace E] [ProperSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem truncatedAuxiliary_congr (ε : ℝ) (t : ℕ) {u v : Fin K → E}
    (hsame : ∀ i, i.val ≤ t → u i = v i) : truncatedAuxiliary ε t u = truncatedAuxiliary ε t v := by
  have hm : maskedFrame t u = maskedFrame t v := by
    funext i
    by_cases hi : i.val ≤ t
    · simp only [maskedFrame, if_pos hi, hsame i hi]
    · simp only [maskedFrame, if_neg hi]
  simp only [truncatedAuxiliary, hm]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem auxiliaryPrefixOracle_congr (ε : ℝ) (t : ℕ) {u v : AuxiliaryBoundedFrame K E}
    (hsame : ∀ i, i.val ≤ t → u.val i = v.val i) (x : E) :
    auxiliaryPrefixOracle ε t u x = auxiliaryPrefixOracle ε t v x := by
  have hf := truncatedAuxiliary_congr ε t hsame
  apply Prod.ext
  · exact congrFun hf x
  · apply Subtype.ext
    apply TopologicalSpace.NonemptyCompacts.ext
    exact congrArg (fun f => subdifferential f x) hf

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem normalizedAuxiliary_fullOracle_locality [FiniteDimensional ℝ E]
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16) {t : ℕ}
    (ht : t < auxiliaryLength ε) {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u)
    (x : E) (hhidden : ∀ i : Fin (auxiliaryLength ε), t ≤ i.val →
      |inner ℝ (u i) x| < auxiliaryEta ε (auxiliaryLength ε)) :
    fullOracle (by norm_num) (by norm_num) (normalizedAuxiliary_admissible hε hsmall hu).lipschitz
      (normalizedAuxiliary_admissible hε hsmall hu).weaklyConvex x =
        auxiliaryPrefixOracle ε t ⟨u, fun i => (hu.norm_eq_one i).le⟩ x := by
  obtain ⟨hval, hset⟩ := normalizedAuxiliary_oracle_locality hε ht u x hhidden
  apply Prod.ext hval
  apply Subtype.ext
  apply TopologicalSpace.NonemptyCompacts.ext
  exact hset

end BoundaryLower
end WC
