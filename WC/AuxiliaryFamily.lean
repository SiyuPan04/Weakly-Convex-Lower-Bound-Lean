import WC.AuxiliaryLocality
import WC.GeneralRotation
import WC.CoreEmbedding
import WC.RotatedOracle

/-! A concrete instance of the proved arbitrary-threshold rotation framework,
using the actual convex auxiliary chain and its complete set-valued oracle. -/

noncomputable section
namespace WC
namespace BoundaryLower

open Rotation.Normalized
open scoped Classical
set_option maxHeartbeats 600000

variable {d K : ℕ} [NeZero d]

def auxiliaryIndices (K t : ℕ) : Finset (Fin K) := Finset.univ.filter (fun i => i.val ≤ t)

theorem auxiliaryIndices_mono (K : ℕ) : Monotone (auxiliaryIndices K) := by
  intro t s hts i hi
  simp only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hts

theorem auxiliaryIndices_proper {t : ℕ} (ht : t + 1 < K) : auxiliaryIndices K t ≠ Finset.univ := by
  intro heq
  have hh : (⟨t + 1, ht⟩ : Fin K) ∈ auxiliaryIndices K t := by rw [heq]; exact Finset.mem_univ _
  simp only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.not_succ_le_self] at hh

theorem auxiliaryIndices_step (t : ℕ) :
    (auxiliaryIndices K (t + 1) \ auxiliaryIndices K t).card ≤ 1 := by
  have hinj : Set.InjOn (fun i : Fin K => i.val) ↑(auxiliaryIndices K (t + 1) \ auxiliaryIndices K t) :=
    fun _ _ _ _ h => Fin.ext h
  have hsubset : (auxiliaryIndices K (t + 1) \ auxiliaryIndices K t).image Fin.val ⊆ {t + 1} := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    simp only [Finset.mem_sdiff, auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injOn hinj, Finset.card_singleton] at hc
  exact hc

def auxiliaryCore (e : Fin K ↪ Fin d) : Finset (Fin d) := Finset.univ.image e
def auxiliaryExposed (e : Fin K ↪ Fin d) (t : ℕ) : Finset (Fin d) := (auxiliaryIndices K t).image e

omit [NeZero d] in
theorem auxiliaryCore_card (e : Fin K ↪ Fin d) : (auxiliaryCore e).card = K := by
  rw [auxiliaryCore, Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]

omit [NeZero d] in
theorem auxiliaryExposed_mono (e : Fin K ↪ Fin d) : Monotone (auxiliaryExposed e) := by
  intro t s hts
  exact Finset.image_subset_image ((auxiliaryIndices_mono K) hts)

omit [NeZero d] in
theorem auxiliaryExposed_subset (e : Fin K ↪ Fin d) (t : ℕ) : auxiliaryExposed e t ⊆ auxiliaryCore e :=
  Finset.image_subset_image (Finset.subset_univ _)

omit [NeZero d] in
theorem auxiliaryExposed_proper (e : Fin K ↪ Fin d) {t : ℕ} (ht : t + 1 < K) :
    auxiliaryExposed e t ≠ auxiliaryCore e := by
  intro heq
  apply auxiliaryIndices_proper ht
  exact (Finset.image_injective e.injective) heq

omit [NeZero d] in
theorem auxiliaryExposed_width (e : Fin K ↪ Fin d) (t : ℕ) :
    (auxiliaryExposed e t \ previous (auxiliaryExposed e) t).card ≤ 5 := by
  cases t with
  | zero =>
    have hsub : auxiliaryIndices K 0 ⊆ Finset.univ.filter (fun i : Fin K => i.val = 0) := by
      intro i hi
      simpa only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.le_zero] using hi
    have hcard : (auxiliaryIndices K 0).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      apply Fin.ext
      simp only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.le_zero] at hi hj
      exact hi.trans hj.symm
    simpa only [previous, Finset.sdiff_empty, auxiliaryExposed,
      Finset.card_image_of_injective _ e.injective] using hcard.trans (by norm_num : 1 ≤ 5)
  | succ t =>
    have heq : auxiliaryExposed e (t + 1) \ auxiliaryExposed e t =
        (auxiliaryIndices K (t + 1) \ auxiliaryIndices K t).image e := by
      exact (Finset.image_sdiff _ _ e.injective).symm
    simp only [previous]
    rw [heq, Finset.card_image_of_injective _ e.injective]
    exact (auxiliaryIndices_step t).trans (by norm_num)

def auxiliaryFrame (e : Fin K ↪ Fin d) (g : Orthogonal d) (i : Fin K) : Ambient d := coordinates g (e i)

omit [NeZero d] in
theorem auxiliaryFrame_orthonormal (e : Fin K ↪ Fin d) (g : Orthogonal d) :
    Orthonormal ℝ (auxiliaryFrame e g) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp e e.injective).comp_linearIsometryEquiv (Frame.act _ g)

def auxiliaryBaseFrame (e : Fin K ↪ Fin d) (i : Fin K) : Ambient d :=
  EuclideanSpace.basisFun (Fin d) ℝ (e i)

omit [NeZero d] in
theorem auxiliaryBaseFrame_orthonormal (e : Fin K ↪ Fin d) : Orthonormal ℝ (auxiliaryBaseFrame e) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp e e.injective

def auxiliaryObjective (ε : ℝ) (e : Fin (auxiliaryLength ε) ↪ Fin d) (g : Orthogonal d) : Ambient d → ℝ :=
  isometricLift (Frame.act _ g).toLinearIsometry (normalizedAuxiliary ε (auxiliaryBaseFrame e))

omit [NeZero d] in
theorem auxiliaryObjective_eq (ε : ℝ) (e : Fin (auxiliaryLength ε) ↪ Fin d) (g : Orthogonal d) :
    auxiliaryObjective ε e g = normalizedAuxiliary ε (auxiliaryFrame e g) := by
  funext x
  have hi (i : Fin (auxiliaryLength ε)) : inner ℝ (auxiliaryBaseFrame e i)
      (isometryProjection (Frame.act _ g).toLinearIsometry x) = inner ℝ (auxiliaryFrame e g i) x :=
    (Frame.act _ g).toContinuousLinearMap.adjoint_inner_right _ _
  have hn : ‖isometryProjection (Frame.act _ g).toLinearIsometry x‖ = ‖x‖ := by
    change ‖(Frame.act _ g).toContinuousLinearMap.adjoint x‖ = ‖x‖
    have hc : (Frame.act _ g).toContinuousLinearMap =
        (Frame.act _ g : Ambient d →L[ℝ] Ambient d) := rfl
    rw [hc]
    rw [(Frame.act _ g).adjoint_eq_symm]
    exact (Frame.act _ g).symm.norm_map x
  have hf : auxiliaryFan (1 / 2) (auxiliaryIntercept ε (auxiliaryLength ε)) (auxiliaryBaseFrame e)
      (isometryProjection (Frame.act _ g).toLinearIsometry x) =
      auxiliaryFan (1 / 2) (auxiliaryIntercept ε (auxiliaryLength ε)) (auxiliaryFrame e g) x := by
    apply congrArg (fun f => sSup (Set.range f))
    funext k
    cases k
    · rfl
    · exact congrArg (fun z => auxiliaryIntercept ε (auxiliaryLength ε) _ - (1 / 2) * z) (hi _)
  change max _ _ = max _ _
  rw [hf]
  simp only [auxiliaryRadial, hn]

omit [NeZero d] in
theorem auxiliaryObjective_admissible {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) (g : Orthogonal d) :
    Admissible 1 1 (ε ^ 2) (auxiliaryObjective ε e g) := by
  have hbase := normalizedAuxiliary_admissible hε hsmall (auxiliaryBaseFrame_orthonormal e)
  exact ⟨isometricLift_weaklyConvex (Frame.act _ g).toLinearIsometry (by norm_num) hbase.weaklyConvex,
    isometricLift_lipschitz (Frame.act _ g).toLinearIsometry (by norm_num) hbase.lipschitz,
    isometricLift_gap (Frame.act _ g).toLinearIsometry hbase.gap⟩

def auxiliaryPrefixFrame (e : Fin K ↪ Fin d) (t : ℕ) (p : Prefix (auxiliaryExposed e t)) :
    AuxiliaryBoundedFrame K (Ambient d) :=
  ⟨fun i => if hi : i.val ≤ t then
      p.val ⟨e i, Finset.mem_image_of_mem e (by simpa only [auxiliaryIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi)⟩ else 0, by
    intro i
    dsimp only
    split_ifs with hi
    · exact (p.property.norm_eq_one _).le
    · simp⟩

omit [NeZero d] in
theorem auxiliaryPrefixFrame_continuous (e : Fin K ↪ Fin d) (t : ℕ) :
    Continuous (auxiliaryPrefixFrame e t) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  by_cases hi : i.val ≤ t
  · change Continuous (fun p : Prefix (auxiliaryExposed e t) => if _ : i.val ≤ t then _ else _)
    simp only [dif_pos hi]
    exact (continuous_apply _).comp continuous_subtype_val
  · change Continuous (fun p : Prefix (auxiliaryExposed e t) => if _ : i.val ≤ t then _ else _)
    simp only [dif_neg hi]
    exact continuous_const

def auxiliaryResponse (ε : ℝ) (e : Fin (auxiliaryLength ε) ↪ Fin d) (t : ℕ)
    (p : Ambient d × Prefix (auxiliaryExposed e t)) : Model.Reply d :=
  auxiliaryPrefixOracle ε t (auxiliaryPrefixFrame e t p.2) p.1

omit [NeZero d] in
theorem auxiliaryResponse_measurable (ε : ℝ) (e : Fin (auxiliaryLength ε) ↪ Fin d) (t : ℕ) :
    @Measurable _ _ (borel _) (borel _) (auxiliaryResponse ε e t) := by
  have hm : Measurable (fun p : Ambient d × Prefix (auxiliaryExposed e t) =>
      (auxiliaryPrefixFrame e t p.2, p.1)) :=
    (((auxiliaryPrefixFrame_continuous e t).comp continuous_snd).measurable.prodMk continuous_fst.measurable)
  have hraw := (auxiliaryPrefixOracle_measurable ε t).comp hm
  have h : Measurable (auxiliaryResponse ε e t) := by
    unfold auxiliaryResponse
    exact hraw
  have hX : borel (Ambient d × Prefix (auxiliaryExposed e t)) =
      (inferInstance : MeasurableSpace (Ambient d × Prefix (auxiliaryExposed e t))) := BorelSpace.measurable_eq.symm
  have hY : borel (Model.Reply d) = (inferInstance : MeasurableSpace (Model.Reply d)) := BorelSpace.measurable_eq.symm
  rw [hX, hY]
  exact h

def auxiliaryOutside (ε : ℝ) (x : Ambient d) : Model.Reply d :=
  fullOracle (G := 1) (ρ := 1) (by norm_num) (by norm_num)
    (auxiliaryRadial_lipschitz (by norm_num) (ε ^ 2) 4)
    (convex_weaklyConvex (by norm_num) (auxiliaryRadial_convex (by norm_num) (ε ^ 2) 4)) x

omit [NeZero d] in
theorem auxiliaryOutside_measurable (ε : ℝ) :
    @Measurable _ _ (borel _) (borel _) (auxiliaryOutside (d := d) ε) := by
  have h : Measurable (auxiliaryOutside (d := d) ε) :=
    fullOracle_measurable (G := 1) (ρ := 1) (by norm_num) (by norm_num) _ _
  have hX : borel (Ambient d) = (inferInstance : MeasurableSpace (Ambient d)) := BorelSpace.measurable_eq.symm
  have hY : borel (Model.Reply d) = (inferInstance : MeasurableSpace (Model.Reply d)) := BorelSpace.measurable_eq.symm
  rw [hX, hY]
  exact h

omit [NeZero d] in
theorem auxiliary_fullOracle_congr {f g : Ambient d → ℝ}
    (hfLip : GloballyLipschitz 1 f) (hgLip : GloballyLipschitz 1 g)
    (hfWC : WeaklyConvex 1 f) (hgWC : WeaklyConvex 1 g) (heq : f = g) (x : Ambient d) :
    fullOracle (by norm_num) (by norm_num) hfLip hfWC x =
      fullOracle (by norm_num) (by norm_num) hgLip hgWC x := by
  subst g
  rfl

theorem auxiliaryObjective_oracle_measurable {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) :
    Measurable (fun p : Orthogonal d × Ambient d =>
      fullOracle (by norm_num) (by norm_num) (auxiliaryObjective_admissible hε hsmall e p.1).lipschitz
        (auxiliaryObjective_admissible hε hsmall e p.1).weaklyConvex p.2) := by
  have hbase := normalizedAuxiliary_admissible hε hsmall (auxiliaryBaseFrame_orthonormal e)
  exact rotated_fullOracle_measurable (by norm_num) (by norm_num) hbase.lipschitz hbase.weaklyConvex

theorem auxiliaryObjective_gradient_measurable {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) :
    Measurable (fun p : Orthogonal d × Ambient d =>
      gradient (moreauEnvelope (1 / 2) (auxiliaryObjective ε e p.1)) p.2) := by
  have hbase := normalizedAuxiliary_admissible hε hsmall (auxiliaryBaseFrame_orthonormal e)
  simpa only [auxiliaryObjective, mul_one] using
    (rotated_moreau_gradient_continuous (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
      hbase.lipschitz hbase.weaklyConvex).measurable

omit [NeZero d] in
theorem auxiliaryObjective_locality {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) {t : ℕ} (ht : t < auxiliaryLength ε)
    (g : Orthogonal d) (x : Ambient d)
    (hhidden : ∀ i ∈ auxiliaryCore e, i ∉ previous (auxiliaryExposed e) t →
      |inner ℝ (coordinates g i) x| < auxiliaryEta ε (auxiliaryLength ε)) :
    fullOracle (by norm_num) (by norm_num) (auxiliaryObjective_admissible hε hsmall e g).lipschitz
      (auxiliaryObjective_admissible hε hsmall e g).weaklyConvex x =
        auxiliaryResponse ε e t (x, framePrefix (auxiliaryExposed e t) g) := by
  have hu := auxiliaryFrame_orthonormal e g
  have hcoord (i : Fin (auxiliaryLength ε)) (hi : t ≤ i.val) :
      |inner ℝ (auxiliaryFrame e g i) x| < auxiliaryEta ε (auxiliaryLength ε) := by
    apply hhidden (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))
    cases t with
    | zero => simp [previous]
    | succ t =>
      simp only [previous, auxiliaryExposed]
      intro hh
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hh
      have hji := e.injective heq
      subst j
      simp only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      omega
  have hobj := auxiliary_fullOracle_congr
    (auxiliaryObjective_admissible hε hsmall e g).lipschitz
    (normalizedAuxiliary_admissible hε hsmall hu).lipschitz
    (auxiliaryObjective_admissible hε hsmall e g).weaklyConvex
    (normalizedAuxiliary_admissible hε hsmall hu).weaklyConvex (auxiliaryObjective_eq ε e g) x
  rw [hobj, normalizedAuxiliary_fullOracle_locality hε hsmall ht hu x hcoord]
  apply auxiliaryPrefixOracle_congr
  intro i hi
  change auxiliaryFrame e g i = if _ : i.val ≤ t then _ else _
  simp only [dif_pos hi]
  rfl

omit [NeZero d] in
theorem auxiliaryObjective_exterior {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) (g : Orthogonal d) (x : Ambient d) (hx : 9 < ‖x‖) :
    fullOracle (by norm_num) (by norm_num) (auxiliaryObjective_admissible hε hsmall e g).lipschitz
      (auxiliaryObjective_admissible hε hsmall e g).weaklyConvex x = auxiliaryOutside ε x ∧
      ‖gradient (moreauEnvelope (1 / 2) (auxiliaryObjective ε e g)) x‖ = 1 := by
  have hu := auxiliaryFrame_orthonormal e g
  have hobj := auxiliaryObjective_eq ε e g
  constructor
  · apply Prod.ext
    · change auxiliaryObjective ε e g x = auxiliaryRadial 1 (ε ^ 2) 4 x
      rw [hobj, normalizedAuxiliary_exterior_value hε hsmall hu (by linarith : 8 < ‖x‖)]
      simp only [auxiliaryRadial, one_mul]
    · apply Subtype.ext
      apply TopologicalSpace.NonemptyCompacts.ext
      change subdifferential (auxiliaryObjective ε e g) x = subdifferential (auxiliaryRadial 1 (ε ^ 2) 4) x
      rw [hobj, normalizedAuxiliary_exterior_subdifferential hε hsmall hu (by linarith : 8 < ‖x‖)]
      ext v
      exact (frechetSubgradient_iff_gradient (auxiliaryRadial_hasGradientAt
        (norm_pos_iff.mp (by linarith : 0 < ‖x‖)))).symm
  · rw [hobj]
    exact normalizedAuxiliary_moreau_exterior hε hsmall hu hx

omit [NeZero d] in
theorem auxiliaryObjective_terminal_barrier {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (e : Fin (auxiliaryLength ε) ↪ Fin d) (g : Orthogonal d) (x : Ambient d)
    (hhidden : ∀ i ∈ auxiliaryCore e, i ∉ auxiliaryExposed e (auxiliaryHorizon ε - 1) →
      |inner ℝ (coordinates g i) x| < auxiliaryEta ε (auxiliaryLength ε)) :
    ε < ‖gradient (moreauEnvelope (1 / 2) (auxiliaryObjective ε e g)) x‖ := by
  have hb := (auxiliaryLength_bounds hε hsmall).1
  have hT : 0 < auxiliaryHorizon ε := by dsimp [auxiliaryHorizon]; omega
  have hTK : auxiliaryHorizon ε < auxiliaryLength ε := by dsimp [auxiliaryHorizon]; omega
  let s : Finset (Fin (auxiliaryLength ε)) := Finset.Ici ⟨auxiliaryHorizon ε, hTK⟩
  have hcard : 7 * auxiliaryLength ε ≤ 8 * s.card := by
    rw [show s.card = auxiliaryLength ε - auxiliaryHorizon ε from Fin.card_Ici _]
    dsimp [auxiliaryHorizon]
    omega
  rw [auxiliaryObjective_eq]
  apply normalizedAuxiliary_moreau_barrier hε hsmall (auxiliaryFrame_orthonormal e g) s hcard x
  intro i hi
  have hiT : auxiliaryHorizon ε ≤ i.val := by simpa only [s, Finset.mem_Ici, Fin.le_def] using hi
  apply le_of_lt
  apply hhidden (e i) (Finset.mem_image_of_mem e (Finset.mem_univ _))
  intro hh
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hh
  have hji := e.injective heq
  subst j
  simp only [auxiliaryIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  omega

def auxiliaryFamily {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    (hd : auxiliaryLength ε ≤ d) :
    Rotation.General.Family d (auxiliaryLength ε) (auxiliaryHorizon ε) := by
  let e : Fin (auxiliaryLength ε) ↪ Fin d := Fin.castLEEmb hd
  have hb := (auxiliaryLength_bounds hε hsmall).1
  refine {
    horizon_positive := ?_
    core := auxiliaryCore e
    core_card := auxiliaryCore_card e
    exposed := auxiliaryExposed e
    exposed_mono := auxiliaryExposed_mono e
    exposed_subset := fun t _ => auxiliaryExposed_subset e t
    exposed_proper := ?_
    width := fun t _ => auxiliaryExposed_width e t
    horizon_bound := ?_
    radius := 9
    tolerance := auxiliaryEta ε (auxiliaryLength ε)
    radius_positive := by norm_num
    tolerance_positive := ?_
    gap := ε ^ 2
    threshold := ε
    threshold_lt_one := by linarith
    objective := auxiliaryObjective ε e
    regularity := auxiliaryObjective_admissible hε hsmall e
    response := auxiliaryResponse ε e
    measurable_response := auxiliaryResponse_measurable ε e
    outside := auxiliaryOutside ε
    measurable_outside := auxiliaryOutside_measurable ε
    locality := ?_
    terminal_barrier := fun g x _ hh => auxiliaryObjective_terminal_barrier hε hsmall e g x hh
    exterior := fun g x hx => auxiliaryObjective_exterior hε hsmall e g x hx
    measurable_oracle := auxiliaryObjective_oracle_measurable hε hsmall e
    measurable_gradient := auxiliaryObjective_gradient_measurable hε hsmall e }
  · dsimp [auxiliaryHorizon]; omega
  · intro t ht
    apply auxiliaryExposed_proper e
    dsimp [auxiliaryHorizon] at ht
    omega
  · dsimp [auxiliaryHorizon]; omega
  · have hKR : (0 : ℝ) < auxiliaryLength ε := by exact_mod_cast (show 0 < auxiliaryLength ε by omega)
    exact div_pos (sq_pos_of_pos hε) (by positivity)
  · intro t ht g x _ hh
    exact auxiliaryObjective_locality hε hsmall e (by dsimp [auxiliaryHorizon] at ht; omega) g x hh

end BoundaryLower
end WC
