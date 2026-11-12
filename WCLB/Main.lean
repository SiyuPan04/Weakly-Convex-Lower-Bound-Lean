import WCLB.Model
import WCLB.RandomizedReduction

/-! `thm:main` of the WCLB manuscript with the explicit constants used
in its scaling proof. The imported normalized families are constructed
and proved, rather than assumed as a certificate. -/

noncomputable section
namespace WCLB

theorem small_accuracy_ratios {G ρ Δ ε : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (haccuracy : ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ))) :
    (2 : ℝ) ^ 18 ≤ G ^ 2 / ε ^ 2 ∧
      (2 : ℝ) ^ 18 ≤ ρ * Δ / ε ^ 2 := by
  have hGacc : ε ≤ (1 / 512 : ℝ) * G :=
    haccuracy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hSacc : ε ≤ (1 / 512 : ℝ) * Real.sqrt (ρ * Δ) :=
    haccuracy.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
  have hGs : (512 * ε) ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 512 * ε) hG.le).mpr (by linarith)
  have hSs : (512 * ε) ^ 2 ≤ Real.sqrt (ρ * Δ) ^ 2 :=
    (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 512 * ε) (Real.sqrt_nonneg _)).mpr (by linarith)
  rw [Real.sq_sqrt (mul_pos hρ hΔ).le] at hSs
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    norm_num
    nlinarith
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    norm_num
    nlinarith

open WC WC.LowerReduction

/-- The explicit lower bound of Theorem 2. The hard dimension is chosen to
satisfy (6.5); randomized reduction and physical scaling give one instance
that defeats the entire trajectory through the chosen horizon. -/
theorem main_explicit {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (haccuracy : ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ)))
    (hgap : Δ ≤ (G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2)))
    (hν : 0 ≤ ν) (hν_one : ν < 1) :
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      WC.Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  obtain ⟨hb, hs⟩ := small_accuracy_ratios hG hρ hΔ hε haccuracy
  let b := G ^ 2 / ε ^ 2
  let r := ρ * Δ / G ^ 2
  let N := ⌊b / 1024⌋₊
  let M := ⌊r * (N : ℝ) / 3⌋₊
  let T := (M - 1) * stagger N
  have hr : 0 < r := div_pos (mul_pos hρ hΔ) (sq_pos_of_pos hG)
  have hbr : b * r = ρ * Δ / ε ^ 2 := by dsimp [b, r]; field_simp
  have hrange : r ≤ Real.exp (b / 200) := by
    apply (div_le_iff₀ (sq_pos_of_pos hG)).mpr
    calc
      ρ * Δ ≤ ρ * ((G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2))) :=
        mul_le_mul_of_nonneg_left hgap hρ.le
      _ = Real.exp (b / 200) * G ^ 2 := by dsimp [b]; field_simp
  obtain ⟨hN, hM, hMmax, hnormgap, hT⟩ :=
    scaling_integer_parameters hb hr (hbr ▸ hs : (2 : ℝ) ^ 18 ≤ b * r) hrange
  have hphysical_gap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ := by
    calc
      (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ (G ^ 2 / ρ) * r :=
        mul_le_mul_of_nonneg_left hnormgap (by positivity)
      _ = Δ := by dsimp [r]; field_simp
  have hNpos : 0 < N := by change 256 ≤ N at hN; omega
  have hMpos : 0 < M := by change 2 ≤ M at hM; omega
  have hbarrier : ε ≤ G * (1 / (32 * Real.sqrt N)) :=
    accuracy_below_barrier hG hε hNpos (scaling_N_bounds hb).2.2.1
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨d, hdim⟩ : ∃ d : ℕ, logarithmicDimensionBound (M * N) T d
      (radialRadius M N) (robustTolerance M N) δ := exists_nat_ge _
  have hd := logarithmic_dimension_positive (Nat.mul_pos hMpos hNpos) hδ hδ1 hdim
  letI : NeZero d := ⟨by omega⟩
  let e := coreEmbedding M N d (by omega : M * N ≤ d)
  have hcomplex : ((T + 1 : ℕ) : ENNReal) ≤ WC.Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
    apply WC.Model.oracleComplexity_lower_bound hG.le hρ.le T
    intro A
    obtain ⟨I, _, hI⟩ := physical_hard_instance_logarithmic e hM hN hMmax hG hρ
      hν hν_one hphysical_gap hbarrier hdim A
    exact ⟨I, hI⟩
  have hid : (1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4 = b ^ 2 * r / (2 : ℝ) ^ 29 := by
    dsimp [b, r]; field_simp
  calc
    _ ≤ ENNReal.ofReal (T : ℝ) := ENNReal.ofReal_le_ofReal (by rw [hid]; exact hT)
    _ = (T : ENNReal) := ENNReal.ofReal_natCast T
    _ ≤ ((T + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.le_succ T
    _ ≤ _ := hcomplex

theorem main : Model.MainTheorem := by
  intro G ρ Δ ε ν hG hρ hΔ hε haccuracy hgap hν hν_one
  exact main_explicit hG hρ hΔ hε haccuracy hgap hν hν_one

/-- Theorem 1 (informal), with its universal implied constant made explicit.
For each fixed positive `G, ρ, Δ`, one positive cutoff works for every `ν`. -/
theorem main_for_sufficiently_small {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ ν : ℝ, 0 ≤ ν → ν < 1 →
      ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
        WC.Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le := by
  let a := (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ))
  let b := G ^ 4 / (200 * ρ * Δ)
  have ha : 0 < a := mul_pos (by norm_num) (lt_min hG (Real.sqrt_pos.mpr (mul_pos hρ hΔ)))
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨min a (min 1 b), lt_min ha (lt_min zero_lt_one hb), ?_⟩
  intro ε hε hcut ν hν hν1
  apply main_explicit hG hρ hΔ hε (hcut.trans (min_le_left _ _)) _ hν hν1
  have hcut' := hcut.trans (min_le_right a (min 1 b))
  have hε1 : ε ≤ 1 := hcut'.trans (min_le_left _ _)
  have hεb : ε ≤ b := hcut'.trans (min_le_right _ _)
  have hbudget := (le_div_iff₀ (by positivity : 0 < 200 * ρ * Δ)).mp hεb
  have hbudget' : ε ^ 2 * (200 * ρ * Δ) ≤ G ^ 4 :=
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)] : ε ^ 2 ≤ ε)
      (by positivity)).trans hbudget
  have hx : ρ * Δ / G ^ 2 ≤ G ^ 2 / (200 * ε ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hbudget']
  have he := Real.add_one_le_exp (G ^ 2 / (200 * ε ^ 2))
  calc
    Δ = (G ^ 2 / ρ) * (ρ * Δ / G ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hx.trans (by linarith)) (by positivity)

/-- Theorem 2 with the exact positive-dimensional instance class of Definition 1. -/
theorem main_positive_dimension {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (haccuracy : ε ≤ (1 / 512 : ℝ) * min G (Real.sqrt (ρ * Δ)))
    (hgap : Δ ≤ (G ^ 2 / ρ) * Real.exp (G ^ 2 / (200 * ε ^ 2)))
    (hν : 0 ≤ ν) (hν_one : ν < 1) :
    ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
      Model.positiveDimensionalComplexity G ρ Δ ε ν hG.le hρ.le := by
  rw [Model.positiveDimensionalComplexity_eq _ _ _ _ _ _ _ hε.le hν]
  exact main_explicit hG hρ hΔ hε haccuracy hgap hν hν_one

/-- Theorem 1 on the positive-dimensional class, including the zero initial-gap case. -/
theorem main_for_sufficiently_small_nonneg_gap {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hΔ : 0 ≤ Δ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ ν : ℝ, 0 ≤ ν → ν < 1 →
      ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * ρ * G ^ 2 * Δ / ε ^ 4) ≤
        Model.positiveDimensionalComplexity G ρ Δ ε ν hG.le hρ.le := by
  rcases hΔ.lt_or_eq with hΔ' | hΔ'
  · obtain ⟨ε₀, h₀, h⟩ := main_for_sufficiently_small hG hρ hΔ'
    refine ⟨ε₀, h₀, ?_⟩
    intro ε hε hcut ν hν hν1
    rw [Model.positiveDimensionalComplexity_eq _ _ _ _ _ _ _ hε.le hν]
    exact h ε hε hcut ν hν hν1
  · subst Δ
    exact ⟨1, zero_lt_one, by intros; simp⟩

end WCLB
