import WC.AuxiliaryBarrier
import Mathlib.Order.Interval.Finset.Fin

/-! Exact normalized appendix parameters for the convex auxiliary chain. -/

noncomputable section
namespace WC
namespace BoundaryLower

open scoped BigOperators

def auxiliaryLength (ε : ℝ) : ℕ := ⌊1 / (8 * ε ^ 2)⌋₊
def auxiliaryHorizon (ε : ℝ) : ℕ := auxiliaryLength ε / 8
def auxiliaryIntercept (ε : ℝ) (K : ℕ) (i : Fin K) : ℝ :=
  ε ^ 2 * (1 - (i.val : ℝ) / (16 * K))
def auxiliaryEta (ε : ℝ) (K : ℕ) : ℝ := ε ^ 2 / (32 * K)

theorem auxiliaryLength_bounds {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16) :
    32 ≤ auxiliaryLength ε ∧ 1 ≤ 10 * (auxiliaryLength ε : ℝ) * ε ^ 2 ∧
      8 * (auxiliaryLength ε : ℝ) * ε ^ 2 ≤ 1 := by
  have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hs : ε ^ 2 ≤ 1 / 256 := by nlinarith
  have hf := Nat.floor_le (by positivity : 0 ≤ 1 / (8 * ε ^ 2))
  have hn := Nat.lt_floor_add_one (1 / (8 * ε ^ 2))
  have h32 : 32 ≤ auxiliaryLength ε := by
    apply Nat.le_floor
    apply (le_div_iff₀ (by positivity : 0 < 8 * ε ^ 2)).mpr
    norm_num
    nlinarith
  have hlow : 1 < 8 * ((auxiliaryLength ε : ℝ) + 1) * ε ^ 2 := by
    simpa only [auxiliaryLength, mul_assoc, mul_comm, mul_left_comm] using
      (div_lt_iff₀ (by positivity : 0 < 8 * ε ^ 2)).mp hn
  have hupp : 8 * (auxiliaryLength ε : ℝ) * ε ^ 2 ≤ 1 := by
    simpa only [auxiliaryLength, mul_assoc, mul_comm, mul_left_comm] using
      (le_div_iff₀ (by positivity : 0 < 8 * ε ^ 2)).mp hf
  exact ⟨h32, by nlinarith, hupp⟩

theorem auxiliaryIntercept_bounds {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 0 < K)
    (i : Fin K) : 15 * ε ^ 2 / 16 < auxiliaryIntercept ε K i ∧
      auxiliaryIntercept ε K i ≤ ε ^ 2 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hi : (i.val : ℝ) < K := by exact_mod_cast i.isLt
  have hi0 : 0 ≤ (i.val : ℝ) := by positivity
  have hd : (i.val : ℝ) / (16 * K) < 1 / 16 := by
    apply (div_lt_iff₀ (by positivity : 0 < 16 * (K : ℝ))).mpr
    nlinarith
  have hd0 : 0 ≤ (i.val : ℝ) / (16 * K) := by positivity
  dsimp [auxiliaryIntercept]
  constructor
  · nlinarith [sq_pos_of_pos hε]
  · nlinarith

theorem auxiliary_hidden_budget {ε : ℝ} (hε : 0 < ε) {K n : ℕ} (hK : 1 ≤ K)
    (hlow : 1 ≤ 10 * (K : ℝ) * ε ^ 2) (hcard : 7 * K ≤ 8 * n) :
    0 ≤ (15 * ε ^ 2 / 16) / (1 / 2) - auxiliaryEta ε K ∧
    ε ^ 2 / 4 < (n : ℝ) * ((15 * ε ^ 2 / 16) / (1 / 2) - auxiliaryEta ε K) ^ 2 := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hKR
  have hη : auxiliaryEta ε K ≤ ε ^ 2 / 32 := by
    unfold auxiliaryEta
    apply (div_le_div_iff₀ (by positivity : 0 < 32 * (K : ℝ)) (by norm_num : (0 : ℝ) < 32)).mpr
    nlinarith [sq_nonneg ε]
  have hm : 7 * ε ^ 2 / 4 ≤ (15 * ε ^ 2 / 16) / (1 / 2) - auxiliaryEta ε K := by
    norm_num
    nlinarith [sq_nonneg ε]
  have hm0 : 0 ≤ (15 * ε ^ 2 / 16) / (1 / 2) - auxiliaryEta ε K := by nlinarith [sq_nonneg ε]
  have hmsq := (sq_le_sq₀ (by positivity : 0 ≤ 7 * ε ^ 2 / 4) hm0).mpr hm
  have hs := mul_le_mul_of_nonneg_left hmsq (show 0 ≤ (n : ℝ) by positivity)
  have hc : 7 * (K : ℝ) ≤ 8 * n := by exact_mod_cast hcard
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (ε ^ 2))
  have hk' := mul_le_mul_of_nonneg_right hlow (sq_nonneg ε)
  exact ⟨hm0, by nlinarith [sq_pos_of_pos hε]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E]

def normalizedAuxiliary (ε : ℝ) (u : Fin (auxiliaryLength ε) → E) : E → ℝ :=
  auxiliaryChain 1 (1 / 2) (ε ^ 2) 4 (auxiliaryIntercept ε (auxiliaryLength ε)) u

omit [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E] in
theorem normalizedAuxiliary_admissible {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u) :
    Admissible 1 1 (ε ^ 2) (normalizedAuxiliary ε u) := by
  have hb := auxiliaryLength_bounds hε hsmall
  exact auxiliaryChain_admissible (by norm_num) (by norm_num) (by norm_num)
    (sq_nonneg ε) (by norm_num)
    (fun i => (auxiliaryIntercept_bounds hε (by omega) i).2) hu

theorem normalizedAuxiliary_moreau_barrier {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u)
    (s : Finset (Fin (auxiliaryLength ε))) (hcard : 7 * auxiliaryLength ε ≤ 8 * s.card)
    (x : E) (hhidden : ∀ i ∈ s, |inner ℝ (u i) x| ≤ auxiliaryEta ε (auxiliaryLength ε)) :
    ε < ‖gradient (moreauEnvelope (1 / 2) (normalizedAuxiliary ε u)) x‖ := by
  have hb := auxiliaryLength_bounds hε hsmall
  have hs : ε ^ 2 ≤ 1 / 256 := by nlinarith
  have hK : 0 < auxiliaryLength ε := by omega
  have hbudget := auxiliary_hidden_budget hε (by omega : 1 ≤ auxiliaryLength ε) hb.2.1 hcard
  have hh := auxiliaryChain_moreau_barrier (G := 1) (A := 1 / 2) (R := 4) (ρ := 1)
    (aMin := 15 * ε ^ 2 / 16) (by norm_num) hε (by norm_num) (by norm_num) hK
    (by nlinarith [hb.2.2]) (by nlinarith) (by norm_num; nlinarith)
    (fun i => by simpa using (auxiliaryIntercept_bounds hε hK i).2) hu s
    (fun i _ => (auxiliaryIntercept_bounds hε hK i).1.le) hbudget.1
    (by simpa using hbudget.2) x hhidden
  simpa only [normalizedAuxiliary, mul_one, one_mul, div_one] using hh

omit [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E] in
theorem auxiliaryFan_norm_upper {K : ℕ} {A a₀ : ℝ} (hA : 0 ≤ A) (ha₀ : 0 ≤ a₀)
    {a : Fin K → ℝ} (ha : ∀ i, a i ≤ a₀) {u : Fin K → E} (hu : Orthonormal ℝ u) (x : E) :
    auxiliaryFan A a u x ≤ a₀ + A * ‖x‖ := by
  apply auxiliaryFan_le (by positivity)
  intro i
  have hi := abs_real_inner_le_norm (u i) x
  rw [hu.norm_eq_one, one_mul] at hi
  have hneg := (neg_le_abs (inner ℝ (u i) x)).trans hi
  nlinarith [ha i]

omit [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E] in
theorem normalizedAuxiliary_radial_dominates {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u) {x : E} (hx : 8 < ‖x‖) :
    auxiliaryFan (1 / 2) (auxiliaryIntercept ε (auxiliaryLength ε)) u x <
      auxiliaryRadial 1 (ε ^ 2) 4 x := by
  have hb := auxiliaryLength_bounds hε hsmall
  have hf := auxiliaryFan_norm_upper (A := 1 / 2) (by norm_num) (sq_nonneg ε)
    (fun i => (auxiliaryIntercept_bounds hε (by omega) i).2) hu x
  dsimp [auxiliaryRadial]
  linarith

omit [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E] in
theorem normalizedAuxiliary_exterior_value {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u) {x : E} (hx : 8 < ‖x‖) :
    normalizedAuxiliary ε u x = ε ^ 2 + (‖x‖ - 4) := by
  simpa only [normalizedAuxiliary, auxiliaryChain, auxiliaryRadial, one_mul] using
    max_eq_right (normalizedAuxiliary_radial_dominates hε hsmall hu hx).le

theorem normalizedAuxiliary_exterior_subdifferential {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u) {x : E} (hx : 8 < ‖x‖) :
    subdifferential (normalizedAuxiliary ε u) x = {(1 / ‖x‖) • x} := by
  have hb := auxiliaryLength_bounds hε hsmall
  have hfan := auxiliaryFan_lipschitz (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (auxiliaryIntercept ε (auxiliaryLength ε)) hu
  have hmax := subdifferential_max_right_of_lt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
    (hfan.mono (by norm_num)) (auxiliaryRadial_lipschitz (E := E) (by norm_num) (ε ^ 2) 4)
    (convex_weaklyConvex le_rfl (auxiliaryFan_convex (1 / 2) (auxiliaryIntercept ε (auxiliaryLength ε)) u))
    (convex_weaklyConvex le_rfl (auxiliaryRadial_convex (E := E) (by norm_num : (0 : ℝ) ≤ 1) (ε ^ 2) 4))
    (normalizedAuxiliary_radial_dominates hε hsmall hu hx)
  change subdifferential (fun y => max (auxiliaryFan (1 / 2) (auxiliaryIntercept ε (auxiliaryLength ε)) u y)
    (auxiliaryRadial 1 (ε ^ 2) 4 y)) x = _
  rw [hmax]
  ext v
  exact frechetSubgradient_iff_gradient (auxiliaryRadial_hasGradientAt (norm_pos_iff.mp (by linarith)))

theorem normalizedAuxiliary_moreau_exterior {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 16)
    {u : Fin (auxiliaryLength ε) → E} (hu : Orthonormal ℝ u) {x : E} (hx : 9 < ‖x‖) :
    ‖gradient (moreauEnvelope (1 / 2) (normalizedAuxiliary ε u)) x‖ = 1 := by
  let H := normalizedAuxiliary ε u
  let p := proximalPoint 1 H x
  have hadm := normalizedAuxiliary_admissible hε hsmall hu
  have hp := proximalPoint_spec (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1) hadm.lipschitz x
  have hdist := hp.displacement_le (by norm_num) (by norm_num) hadm.weaklyConvex hadm.lipschitz
  have hnorm := norm_sub_norm_le x p
  have hpout : 8 < ‖p‖ := by norm_num at hdist; linarith
  have hv := (hp.weakSubgradient (by norm_num) hadm.weaklyConvex).frechet (by norm_num)
  have heq : (2 : ℝ) • (x - p) = (1 / ‖p‖) • p := by
    have hmem : (2 : ℝ) • (x - p) ∈ subdifferential H p := by
      change FrechetSubgradient H p _
      simpa only [mul_one] using hv
    rw [show subdifferential H p = {(1 / ‖p‖) • p} from
      normalizedAuxiliary_exterior_subdifferential hε hsmall hu hpout] at hmem
    exact hmem
  have hg := moreau_gradient_eq (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1)
    hadm.lipschitz hadm.weaklyConvex x
  norm_num at hg
  rw [hg, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / ‖p‖)]
  exact div_mul_cancel₀ 1 (by linarith : ‖p‖ ≠ 0)

end BoundaryLower
end WC
