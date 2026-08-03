import WeaklyConvexLowerBound.Basic
import WeaklyConvexLowerBound.Foundation.Arithmetic

/-!
# Parameter arithmetic for the framework reduction

This file verifies the floor and constant calculations in the proof of the
framework-reduction proposition (TeX lines 888--1020).  In particular, the
paper's choices of `N` and `M` form an admissible pair, and the normalized
horizon lower bound scales to the claimed constant `1 / 47185920`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- The small-accuracy constant in the framework-reduction proposition. -/
def paperC0 : ℝ := 1 / 7680

/-- The explicit constant in the resulting oracle lower bound. -/
def paperC1 : ℝ := 1 / 47185920

/-- The dimensionless ratio `min {ρ Δ / G², 1}` used in the construction. -/
def parameterR (G ρ Δ : ℝ) : ℝ :=
  min (ρ * Δ / G ^ 2) 1

/-- The coordinate length selected by the first floor. -/
def parameterN (G ε : ℝ) : Nat :=
  ⌊G ^ 2 / (64 * ε ^ 2)⌋₊

/-- Flooring never increases the raw inner-chain length. -/
theorem parameterN_upper {G ε : ℝ} (hε : 0 < ε) :
    (parameterN G ε : ℝ) ≤ G ^ 2 / (64 * ε ^ 2) := by
  unfold parameterN
  apply Nat.floor_le
  positivity

/-- The paper's choice of `N` makes the scaled terminal obstruction at least
the requested accuracy.  This is the square-root inequality used at TeX
lines 991--995. -/
theorem epsilon_le_terminal_threshold {G ε : ℝ} {N : Nat}
    (hG : 0 < G) (hε : 0 < ε) (hN : 0 < N)
    (hNupper : (N : ℝ) ≤ G ^ 2 / (64 * ε ^ 2)) :
    ε ≤ G / (8 * Real.sqrt N) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNR
  rw [le_div_iff₀ (mul_pos (by norm_num) hsqrt)]
  have hscale : 0 ≤ 64 * ε ^ 2 := by positivity
  have hsqBound : 64 * ε ^ 2 * (N : ℝ) ≤ G ^ 2 := by
    calc
      64 * ε ^ 2 * (N : ℝ) ≤
          64 * ε ^ 2 * (G ^ 2 / (64 * ε ^ 2)) :=
        mul_le_mul_of_nonneg_left hNupper hscale
      _ = G ^ 2 := by field_simp [hε.ne']
  have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNR.le
  have hleft : 0 ≤ ε * (8 * Real.sqrt (N : ℝ)) := by positivity
  nlinarith

/-- The number of blocks selected by the second floor. -/
def parameterM (G ρ Δ ε : ℝ) : Nat :=
  ⌊(parameterN G ε : ℝ) * parameterR G ρ Δ / 12⌋₊

theorem paperC0_pos : 0 < paperC0 := by
  norm_num [paperC0]

theorem paperC1_pos : 0 < paperC1 := by
  norm_num [paperC1]

theorem parameterR_pos {G ρ Δ : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) :
    0 < parameterR G ρ Δ := by
  unfold parameterR
  rw [lt_min_iff]
  constructor
  · exact div_pos (mul_pos hρ hΔ) (sq_pos_of_pos hG)
  · norm_num

theorem parameterR_nonneg {G ρ Δ : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) :
    0 ≤ parameterR G ρ Δ :=
  (parameterR_pos hG hρ hΔ).le

theorem parameterR_le_one (G ρ Δ : ℝ) :
    parameterR G ρ Δ ≤ 1 := by
  exact min_le_right _ _

/-- Multiplying the clipped ratio by `G²` recovers the minimum appearing in
the final lower bound. -/
theorem G_sq_mul_parameterR {G ρ Δ : ℝ} (hG : 0 < G) :
    G ^ 2 * parameterR G ρ Δ = min (ρ * Δ) (G ^ 2) := by
  have hGsq : 0 < G ^ 2 := sq_pos_of_pos hG
  by_cases h : ρ * Δ ≤ G ^ 2
  · have hdiv : ρ * Δ / G ^ 2 ≤ 1 := by
      apply (div_le_iff₀ hGsq).2
      simpa using h
    rw [min_eq_left h]
    simp only [parameterR, min_eq_left hdiv]
    field_simp [hG.ne']
    <;> ring
  · have hrev : G ^ 2 ≤ ρ * Δ := le_of_not_ge h
    have hdiv : 1 ≤ ρ * Δ / G ^ 2 := by
      apply (le_div_iff₀ hGsq).2
      simpa using hrev
    simp only [parameterR, min_eq_right hdiv, min_eq_right hrev, mul_one]

/-- The accuracy hypothesis is equivalently strong enough to put the minimum
over `ε²` above `7680`. -/
theorem accuracy_min_div_sq_lower {G ρ Δ ε : ℝ}
    (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    7680 ≤ min (G ^ 2) (ρ * Δ) / ε ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  norm_num [paperC0] at hacc
  nlinarith

/-- Before flooring, the first dimension parameter is at least `120`. -/
theorem raw_parameterN_ge_120 {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    120 ≤ G ^ 2 / (64 * ε ^ 2) := by
  have hmin := accuracy_min_div_sq_lower hε hacc
  have hminle : min (G ^ 2) (ρ * Δ) ≤ G ^ 2 := min_le_left _ _
  have hscaled : 7680 * ε ^ 2 ≤ min (G ^ 2) (ρ * Δ) := by
    rw [le_div_iff₀ (sq_pos_of_pos hε)] at hmin
    exact hmin
  rw [le_div_iff₀ (by positivity : 0 < 64 * ε ^ 2)]
  nlinarith

/-- The first floor loses at most a factor of two in the stated regime. -/
theorem parameterN_lower {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    G ^ 2 / (128 * ε ^ 2) ≤ (parameterN G ε : ℝ) := by
  have hraw := raw_parameterN_ge_120 hG hρ hΔ hε hacc
  have hfloor := WeaklyConvexLowerBound.Foundation.half_le_natFloor
    (by linarith : 2 ≤ G ^ 2 / (64 * ε ^ 2))
  change G ^ 2 / (128 * ε ^ 2) ≤
    (⌊G ^ 2 / (64 * ε ^ 2)⌋₊ : ℝ)
  calc
    G ^ 2 / (128 * ε ^ 2) =
        (G ^ 2 / (64 * ε ^ 2)) / 2 := by ring
    _ ≤ _ := hfloor

theorem parameterN_ge_60 {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    60 ≤ parameterN G ε := by
  have hraw := raw_parameterN_ge_120 hG hρ hΔ hε hacc
  have hfloor := WeaklyConvexLowerBound.Foundation.half_le_natFloor
    (by linarith : 2 ≤ G ^ 2 / (64 * ε ^ 2))
  have hreal : (60 : ℝ) ≤ (parameterN G ε : ℝ) := by
    change (60 : ℝ) ≤ (⌊G ^ 2 / (64 * ε ^ 2)⌋₊ : ℝ)
    linarith
  exact_mod_cast hreal

/-- The product `N r` remains at least the minimum divided by the floor-loss
factor `128`. -/
theorem parameterN_mul_R_lower {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    min (G ^ 2) (ρ * Δ) / (128 * ε ^ 2) ≤
      (parameterN G ε : ℝ) * parameterR G ρ Δ := by
  have hN := parameterN_lower hG hρ hΔ hε hacc
  have hR0 := parameterR_nonneg hG hρ hΔ
  calc
    min (G ^ 2) (ρ * Δ) / (128 * ε ^ 2) =
        (G ^ 2 / (128 * ε ^ 2)) * parameterR G ρ Δ := by
      rw [min_comm, ← G_sq_mul_parameterR hG]
      ring
    _ ≤ (parameterN G ε : ℝ) * parameterR G ρ Δ :=
      mul_le_mul_of_nonneg_right hN hR0

theorem parameterN_mul_R_ge_60 {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    60 ≤ (parameterN G ε : ℝ) * parameterR G ρ Δ := by
  have hmin := accuracy_min_div_sq_lower hε hacc
  have hscaled : (60 : ℝ) ≤
      min (G ^ 2) (ρ * Δ) / (128 * ε ^ 2) := by
    rw [le_div_iff₀ (by positivity : 0 < 128 * ε ^ 2)]
    rw [le_div_iff₀ (sq_pos_of_pos hε)] at hmin
    nlinarith
  exact hscaled.trans (parameterN_mul_R_lower hG hρ hΔ hε hacc)

/-- The second floor also loses at most a factor of two. -/
theorem parameterM_lower {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    (parameterN G ε : ℝ) * parameterR G ρ Δ / 24 ≤
      (parameterM G ρ Δ ε : ℝ) := by
  have hNr := parameterN_mul_R_ge_60 hG hρ hΔ hε hacc
  have hfloor := WeaklyConvexLowerBound.Foundation.half_le_natFloor
    (by linarith :
      2 ≤ (parameterN G ε : ℝ) * parameterR G ρ Δ / 12)
  change (parameterN G ε : ℝ) * parameterR G ρ Δ / 24 ≤
    (⌊(parameterN G ε : ℝ) * parameterR G ρ Δ / 12⌋₊ : ℝ)
  calc
    (parameterN G ε : ℝ) * parameterR G ρ Δ / 24 =
        ((parameterN G ε : ℝ) * parameterR G ρ Δ / 12) / 2 := by ring
    _ ≤ _ := hfloor

theorem parameterM_ge_5 {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    5 ≤ parameterM G ρ Δ ε := by
  unfold parameterM
  apply Nat.le_floor
  have hNr := parameterN_mul_R_ge_60 hG hρ hΔ hε hacc
  linarith

theorem twelve_parameterM_le_parameterN {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) :
    12 * parameterM G ρ Δ ε ≤ parameterN G ε := by
  have hR0 := parameterR_nonneg hG hρ hΔ
  have hR1 := parameterR_le_one G ρ Δ
  have hMcast : (parameterM G ρ Δ ε : ℝ) ≤
      (parameterN G ε : ℝ) * parameterR G ρ Δ / 12 := by
    unfold parameterM
    apply Nat.floor_le
    positivity
  have hNrle : (parameterN G ε : ℝ) * parameterR G ρ Δ ≤
      (parameterN G ε : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hR1
      (Nat.cast_nonneg (parameterN G ε) : (0 : ℝ) ≤ parameterN G ε)
  have hreal : (12 : ℝ) * (parameterM G ρ Δ ε : ℝ) ≤
      (parameterN G ε : ℝ) := by
    nlinarith
  exact_mod_cast hreal

/-- The floor-selected pair satisfies exactly the admissibility requirements
used by the normalized hard-instance hypothesis. -/
theorem parameters_admissible {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    Admissible (parameterM G ρ Δ ε) (parameterN G ε) := by
  refine
    { N_ge := parameterN_ge_60 hG hρ hΔ hε hacc
      M_ge := ?_
      twelve_M_le := twelve_parameterM_le_parameterN hG hρ hΔ }
  have hM := parameterM_ge_5 hG hρ hΔ hε hacc
  omega

/-- Arithmetic form of the paper's horizon calculation.  The hypothesis and
conclusion explicitly cast the natural-valued horizons and dimensions to
`ℝ`, so no truncating natural-number division is hidden in the statement. -/
theorem horizon_lower_bound {G ρ Δ ε : ℝ} {H : Nat}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ))
    (hH : (((parameterM G ρ Δ ε * parameterN G ε : Nat) : ℝ) / 120) ≤
      (H : ℝ)) :
    paperC1 * (G ^ 2 * min (ρ * Δ) (G ^ 2) / ε ^ 4) ≤ (H : ℝ) := by
  have hN := parameterN_lower hG hρ hΔ hε hacc
  have hM := parameterM_lower hG hρ hΔ hε hacc
  have hR0 := parameterR_nonneg hG hρ hΔ
  have hraw0 : 0 ≤ G ^ 2 / (128 * ε ^ 2) := by positivity
  have hN0 : (0 : ℝ) ≤ parameterN G ε := Nat.cast_nonneg _
  have hNsq : (G ^ 2 / (128 * ε ^ 2)) ^ 2 ≤
      (parameterN G ε : ℝ) ^ 2 := by
    nlinarith
  have hNsqR : (G ^ 2 / (128 * ε ^ 2)) ^ 2 * parameterR G ρ Δ ≤
      (parameterN G ε : ℝ) ^ 2 * parameterR G ρ Δ :=
    mul_le_mul_of_nonneg_right hNsq hR0
  have hMN : (parameterN G ε : ℝ) ^ 2 * parameterR G ρ Δ / 24 ≤
      (parameterM G ρ Δ ε : ℝ) * (parameterN G ε : ℝ) := by
    calc
      (parameterN G ε : ℝ) ^ 2 * parameterR G ρ Δ / 24 =
          ((parameterN G ε : ℝ) * parameterR G ρ Δ / 24) *
            (parameterN G ε : ℝ) := by ring
      _ ≤ (parameterM G ρ Δ ε : ℝ) * (parameterN G ε : ℝ) :=
        mul_le_mul_of_nonneg_right hM hN0
  calc
    paperC1 * (G ^ 2 * min (ρ * Δ) (G ^ 2) / ε ^ 4) =
        (G ^ 2 / (128 * ε ^ 2)) ^ 2 * parameterR G ρ Δ / 2880 := by
      rw [← G_sq_mul_parameterR hG]
      unfold paperC1
      field_simp [hε.ne']
      <;> ring
    _ ≤ (parameterN G ε : ℝ) ^ 2 * parameterR G ρ Δ / 2880 :=
      div_le_div_of_nonneg_right hNsqR (by norm_num)
    _ = ((parameterN G ε : ℝ) ^ 2 * parameterR G ρ Δ / 24) / 120 := by
      ring
    _ ≤ ((parameterM G ρ Δ ε : ℝ) * (parameterN G ε : ℝ)) / 120 :=
      div_le_div_of_nonneg_right hMN (by norm_num)
    _ = (((parameterM G ρ Δ ε * parameterN G ε : Nat) : ℝ) / 120) := by
      norm_num
    _ ≤ (H : ℝ) := hH

end

end WeaklyConvexLowerBound


