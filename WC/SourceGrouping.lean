import WC.NearSourceMixture
import WC.MixtureAggregation
import Mathlib.Analysis.Convex.Combination

/-! Constructed radius groups for the actual complete majorant subdifferential. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

def chainNearRadius (N : ℕ) : ℝ := 1 / (288 * Real.sqrt (N : ℝ))

def sourceRadiusBand (B : ℕ) (r d : ℝ) (hd : d ≤ (8 : ℝ) ^ B * r) : Fin (B + 1) :=
  let hex : ∃ j : ℕ, d ≤ (8 : ℝ) ^ j * r := ⟨B, hd⟩
  ⟨Nat.find hex, Nat.lt_succ_of_le (Nat.find_min' hex hd)⟩

theorem sourceRadiusBand_upper {B : ℕ} {r d : ℝ} (hd : d ≤ (8 : ℝ) ^ B * r) :
    d ≤ (8 : ℝ) ^ (sourceRadiusBand B r d hd).val * r :=
  Nat.find_spec (show ∃ j : ℕ, d ≤ (8 : ℝ) ^ j * r from ⟨B, hd⟩)

theorem sourceRadiusBand_near {B : ℕ} {r d : ℝ} (hd : d ≤ (8 : ℝ) ^ B * r)
    (hzero : sourceRadiusBand B r d hd = 0) : d ≤ r := by
  have h := sourceRadiusBand_upper hd
  rw [hzero] at h
  simpa using h

theorem sourceRadiusBand_remote {B : ℕ} {r d : ℝ} (hd : d ≤ (8 : ℝ) ^ B * r)
    (hzero : sourceRadiusBand B r d hd ≠ 0) :
    (8 : ℝ) ^ ((sourceRadiusBand B r d hd).val - 1) * r < d ∧
      d ≤ 8 * ((8 : ℝ) ^ ((sourceRadiusBand B r d hd).val - 1) * r) := by
  have hjpos : 0 < (sourceRadiusBand B r d hd).val :=
    Nat.pos_of_ne_zero (fun h => hzero (Fin.ext h))
  let hex : ∃ j : ℕ, d ≤ (8 : ℝ) ^ j * r := ⟨B, hd⟩
  have hjpos' : 0 < Nat.find hex := hjpos
  have hmin := Nat.find_min hex (Nat.sub_lt hjpos' (by norm_num : 0 < 1))
  constructor
  · exact lt_of_not_ge hmin
  · have h := sourceRadiusBand_upper hd
    have heq : (8 : ℝ) ^ (sourceRadiusBand B r d hd).val * r =
        8 * ((8 : ℝ) ^ ((sourceRadiusBand B r d hd).val - 1) * r) := by
      conv_lhs => rw [← Nat.sub_add_cancel hjpos]
      rw [pow_succ]
      ring
    rwa [heq] at h

def sourceGroupMass {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) (j : κ) : ℝ :=
  ∑ i : {i // band i = j}, weights i.val

def sourceGroupVector {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) (g : ι → E) (j : κ) : E :=
  ∑ i : {i // band i = j}, weights i.val • g i.val

theorem sourceGroupMass_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (band : ι → κ) (weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i) (j : κ) :
    0 ≤ sourceGroupMass band weights j := Finset.sum_nonneg fun i _ => hw i.val

theorem sourceGroupMass_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) :
    (∑ j, sourceGroupMass band weights j) = ∑ i, weights i := Fintype.sum_fiberwise band weights

theorem sourceGroupVector_sum {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) (g : ι → E) :
    (∑ j, sourceGroupVector band weights g j) = ∑ i, weights i • g i :=
  Fintype.sum_fiberwise band (fun i => weights i • g i)

theorem sourceGroupVector_zero_of_mass_zero {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) (g : ι → E)
    (hw : ∀ i, 0 ≤ weights i) (j : κ) (hj : sourceGroupMass band weights j = 0) :
    sourceGroupVector band weights g j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hw k.val) (Finset.mem_univ i)
  change weights i.val ≤ sourceGroupMass band weights j at hle
  rw [hj] at hle
  have hz : weights i.val = 0 := le_antisymm hle (hw i.val)
  simp [hz]

theorem sourceGroupVector_normalized {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (band : ι → κ) (weights : ι → ℝ) (g : ι → E)
    (j : κ) (hj : sourceGroupMass band weights j ≠ 0) :
    sourceGroupVector band weights g j = sourceGroupMass band weights j •
      (∑ i : {i // band i = j}, (weights i.val / sourceGroupMass band weights j) • g i.val) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, mul_div_cancel₀ _ hj]

theorem sourceGroupNormalized_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (band : ι → κ) (weights : ι → ℝ) (j : κ) (hj : sourceGroupMass band weights j ≠ 0) :
    (∑ i : {i // band i = j}, weights i.val / sourceGroupMass band weights j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hj

theorem chainNearRadius_pos {N : ℕ} (hN : 0 < N) : 0 < chainNearRadius N := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  unfold chainNearRadius
  positivity

theorem chainNearRadius_margin {N : ℕ} (hN : 0 < N) :
    1 / (5 * Real.sqrt (N : ℝ)) ≤ 1 / (4 * Real.sqrt (N : ℝ)) - 3 * (9 / 2 : ℝ) * chainNearRadius N := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr h
  have heq : 1 / (4 * Real.sqrt (N : ℝ)) - 3 * (9 / 2 : ℝ) * chainNearRadius N -
      1 / (5 * Real.sqrt (N : ℝ)) = 1 / (320 * Real.sqrt (N : ℝ)) := by
    unfold chainNearRadius
    field_simp
    ring
  have hn : 0 ≤ 1 / (320 * Real.sqrt (N : ℝ)) := by positivity
  linarith

theorem chain_finiteSourceMixture_norm_sq {M N B : ℕ} {ι : Type*} [Fintype ι]
    (hN : 256 ≤ N) (weights : ι → ℝ) (y g : ι → ChainSpace M N) (z : ChainSpace M N)
    (hw : ∀ i, 0 ≤ weights i) (hwsum : ∑ i, weights i = 1)
    (hsource : ∀ i, y i ∈ majorantSources coupledFunction 2 z)
    (hgradient : ∀ i, g i ∈ subdifferential coupledFunction (y i))
    (hcoverage : ∀ i, ‖z - y i‖ ≤ (8 : ℝ) ^ B * chainNearRadius N)
    (hfar : ∀ q ∈ terminalRegion, chainNearRadius N < ‖z - q‖) :
    1 / (25 * (N : ℝ) + 8 * (B : ℝ)) ≤ ‖∑ i, weights i • g i‖ ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hr : 0 < chainNearRadius N := chainNearRadius_pos hNpos
  let band (i : ι) : Fin (B + 1) := sourceRadiusBand B (chainNearRadius N) ‖z - y i‖ (hcoverage i)
  let mass := sourceGroupMass band weights
  let vectors := sourceGroupVector band weights g
  have hm (j : Fin (B + 1)) : 0 ≤ mass j := sourceGroupMass_nonneg band weights hw j
  have htotal : ∑ j, mass j = 1 := (sourceGroupMass_sum band weights).trans hwsum
  have hcoords (j : Fin (B + 1)) (k : Fin M × Fin N) : vectors j k ≤ 0 := by
    change (∑ i : {i // band i = j}, weights i.val • g i.val) k ≤ 0
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    exact Finset.sum_nonpos fun (i : {i // band i = j}) _ => mul_nonpos_of_nonneg_of_nonpos (hw i.val)
      (coupledFunction_subgradient_nonpos hNpos (hgradient i.val) k)
  have hnear : mass 0 ^ 2 / (25 * (N : ℝ)) ≤ ‖vectors 0‖ ^ 2 := by
    by_cases hzero : mass 0 = 0
    · have hvzero := sourceGroupVector_zero_of_mass_zero band weights g hw 0 hzero
      change mass 0 ^ 2 / (25 * (N : ℝ)) ≤ ‖sourceGroupVector band weights g 0‖ ^ 2
      rw [hzero, hvzero]
      norm_num
    have hmasspos : 0 < mass 0 := lt_of_le_of_ne (hm 0) (Ne.symm hzero)
    let nw (i : {i // band i = 0}) := weights i.val / mass 0
    let ng (i : {i // band i = 0}) := g i.val
    have hnw : ∀ i, 0 ≤ nw i := fun i => div_nonneg (hw i.val) (hm 0)
    have hnwsum : ∑ i, nw i = 1 := sourceGroupNormalized_sum band weights 0 hzero
    have hnorm := chain_nearSourceMixture_lower_bound hNpos hr.le nw hnw hnwsum
      (fun i => y i.val) ng z (fun i => hsource i.val) (fun i => hgradient i.val)
      (fun i => sourceRadiusBand_near (hcoverage i.val) i.property) hfar
    have hlower : 1 / (5 * Real.sqrt (N : ℝ)) ≤ ‖∑ i, nw i • ng i‖ :=
      (chainNearRadius_margin hNpos).trans hnorm
    have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
    have hid : (1 / (5 * Real.sqrt (N : ℝ))) ^ 2 = 1 / (25 * (N : ℝ)) := by
      field_simp
      nlinarith [Real.sq_sqrt hNR.le]
    have hsquare := (sq_le_sq₀ (show 0 ≤ 1 / (5 * Real.sqrt (N : ℝ)) by positivity)
      (norm_nonneg (∑ i, nw i • ng i))).mpr hlower
    rw [hid] at hsquare
    change mass 0 ^ 2 / (25 * (N : ℝ)) ≤ ‖sourceGroupVector band weights g 0‖ ^ 2
    rw [sourceGroupVector_normalized band weights g 0 hzero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      mass 0 ^ 2 / (25 * (N : ℝ)) = mass 0 ^ 2 * (1 / (25 * (N : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (mass 0))
  have hremote (j : Fin (B + 1)) (hj : j ≠ 0) : mass j ^ 2 / 8 ≤ ‖vectors j‖ ^ 2 := by
    by_cases hzero : mass j = 0
    · have hvzero := sourceGroupVector_zero_of_mass_zero band weights g hw j hzero
      change mass j ^ 2 / 8 ≤ ‖sourceGroupVector band weights g j‖ ^ 2
      rw [hzero, hvzero]
      norm_num
    let nw (i : {i // band i = j}) := weights i.val / mass j
    let ng (i : {i // band i = j}) := g i.val
    have hnw : ∀ i, 0 ≤ nw i := fun i => div_nonneg (hw i.val) (hm j)
    have hnwsum : ∑ i, nw i = 1 := sourceGroupNormalized_sum band weights j hzero
    let a := (8 : ℝ) ^ (j.val - 1) * chainNearRadius N
    have ha : 0 < a := mul_pos (pow_pos (by norm_num) _) hr
    have hrange (i : {i // band i = j}) : a < ‖z - y i.val‖ ∧ ‖z - y i.val‖ ≤ 8 * a := by
      have hneq : sourceRadiusBand B (chainNearRadius N) ‖z - y i.val‖ (hcoverage i.val) ≠ 0 := by
        change band i.val ≠ 0
        rw [i.property]
        exact hj
      have h := sourceRadiusBand_remote (hcoverage i.val) hneq
      change (8 : ℝ) ^ ((band i.val).val - 1) * chainNearRadius N < ‖z - y i.val‖ ∧
        ‖z - y i.val‖ ≤ 8 * ((8 : ℝ) ^ ((band i.val).val - 1) * chainNearRadius N) at h
      rw [i.property] at h
      exact h
    have hsquare := remote_source_band_mixture hN ha nw (fun i => y i.val) ng hnw hnwsum
      (fun i => hsource i.val) (fun i => hgradient i.val) hrange
    change mass j ^ 2 / 8 ≤ ‖sourceGroupVector band weights g j‖ ^ 2
    rw [sourceGroupVector_normalized band weights g j hzero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      mass j ^ 2 / 8 = mass j ^ 2 * (1 / 8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (mass j))
  have h := near_remote_group_aggregation hNR mass vectors htotal hcoords hnear hremote
  rwa [sourceGroupVector_sum] at h

/-- The pointwise stationarity barrier for the entire actual Lipschitz-majorant subdifferential. -/
theorem chainMajorant_subgradient_norm_sq_lower {M N B : ℕ} (hN : 256 ≤ N)
    (z : ChainSpace M N) (hcoverage : chainSourceRadius M N ≤ (8 : ℝ) ^ B * chainNearRadius N)
    (hfar : ∀ q ∈ terminalRegion, chainNearRadius N < ‖z - q‖)
    {v : ChainSpace M N} (hv : v ∈ subdifferential chainMajorant z) :
    1 / (25 * (N : ℝ) + 8 * (B : ℝ)) ≤ ‖v‖ ^ 2 := by
  rw [chainMajorant_subdifferential hN, mem_convexHull_iff_exists_fintype] at hv
  obtain ⟨ι, inst, weights, g, hw, hsum, hslopes, hvec⟩ := hv
  letI : Fintype ι := inst
  choose y hy hg using hslopes
  have h := chain_finiteSourceMixture_norm_sq (B := B) hN weights y g z hw hsum hy hg
    (fun i => (chain_source_radius hN (hy i)).trans hcoverage) hfar
  rwa [hvec] at h

end WC
