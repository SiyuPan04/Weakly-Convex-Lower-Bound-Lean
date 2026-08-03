import WeaklyConvexLowerBound.CoreFunctions

/-!
# Smooth block progress

This file formalizes the progress carrier from TeX lines 1121--1127 and the
regularity calculation in Lemma `progress-regularity`.  Euclidean estimates
are stated using squared norms, avoiding any auxiliary square-root algebra.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The progress made by a single block. -/
def psi {N : Nat} (u : Fin N → ℝ) : ℝ :=
  (∑ j, q ((N : ℝ) * u j / 4)) / (N : ℝ)

/-- The explicit coordinate formula for the gradient of `psi`. -/
def psiGrad {N : Nat} (u : Fin N → ℝ) : Fin N → ℝ :=
  fun j ↦ qPrime ((N : ℝ) * u j / 4) / 4

@[simp] theorem psiGrad_apply {N : Nat} (u : Fin N → ℝ) (j : Fin N) :
    psiGrad u j = qPrime ((N : ℝ) * u j / 4) / 4 := rfl

theorem psi_nonneg {N : Nat} (u : Fin N → ℝ) : 0 ≤ psi u := by
  unfold psi
  exact div_nonneg
    (Finset.sum_nonneg fun j _ ↦ q_nonneg ((N : ℝ) * u j / 4))
    (Nat.cast_nonneg N)

theorem psi_le_one {N : Nat} (hN : 0 < N) (u : Fin N → ℝ) : psi u ≤ 1 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold psi
  rw [div_le_iff₀ hNreal]
  have hsum : (∑ j, q ((N : ℝ) * u j / 4)) ≤
      ∑ _j : Fin N, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact q_le_one ((N : ℝ) * u j / 4)
  simpa using hsum

theorem psi_mem_unitInterval {N : Nat} (hN : 0 < N) (u : Fin N → ℝ) :
    psi u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨psi_nonneg u, psi_le_one hN u⟩

theorem psiGrad_nonneg {N : Nat} (u : Fin N → ℝ) (j : Fin N) :
    0 ≤ psiGrad u j := by
  rw [psiGrad_apply]
  exact div_nonneg (qPrime_nonneg _) (by norm_num)

theorem psiGrad_le_three_eighths {N : Nat} (u : Fin N → ℝ) (j : Fin N) :
    psiGrad u j ≤ (3 : ℝ) / 8 := by
  rw [psiGrad_apply]
  have hq := qPrime_le_three_halves ((N : ℝ) * u j / 4)
  linarith

/-- Squared Euclidean version of `‖∇psi(u)‖ ≤ 3 sqrt(N) / 8`. -/
theorem psiGrad_vecSq_le {N : Nat} (u : Fin N → ℝ) :
    WeaklyConvexLowerBound.Foundation.vecSq (psiGrad u) ≤ 9 * (N : ℝ) / 64 := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  calc
    (∑ j, psiGrad u j ^ 2) ≤ ∑ _j : Fin N, ((3 : ℝ) / 8) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h0 := psiGrad_nonneg u j
      have h1 := psiGrad_le_three_eighths u j
      nlinarith
    _ = 9 * (N : ℝ) / 64 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- Embed a vector into one chosen block and set every other block to zero. -/
def singleBlock {M N : Nat} (m : Fin M) (v : Fin N → ℝ) : BlockVec M N :=
  fun m' j ↦ if m' = m then v j else 0

theorem blockSq_singleBlock {M N : Nat} (m : Fin M) (v : Fin N → ℝ) :
    blockSq (singleBlock m v) = WeaklyConvexLowerBound.Foundation.vecSq v := by
  classical
  simp [blockSq, singleBlock, WeaklyConvexLowerBound.Foundation.vecSq,
    WeaklyConvexLowerBound.Foundation.vecSq]

/-- The same gradient estimate after viewing a one-block gradient in the full
`M × N` block space. -/
theorem blockSq_singleBlock_psiGrad_le {M N : Nat} (m : Fin M)
    (u : Fin N → ℝ) :
    blockSq (singleBlock m (psiGrad u)) ≤ 9 * (N : ℝ) / 64 := by
  rw [blockSq_singleBlock]
  exact psiGrad_vecSq_le u

/-- Coordinatewise Lipschitz estimate obtained from `Lip(qPrime) ≤ 6`. -/
theorem psiGrad_coord_abs_sub_le {N : Nat} (u v : Fin N → ℝ) (j : Fin N) :
    |psiGrad u j - psiGrad v j| ≤
      (3 * (N : ℝ) / 8) * |u j - v j| := by
  let a : ℝ := (N : ℝ) * u j / 4
  let b : ℝ := (N : ℝ) * v j / 4
  have hq : |qPrime a - qPrime b| ≤ 6 * |a - b| :=
    qPrime_abs_sub_le a b
  have hab : |a - b| = (N : ℝ) / 4 * |u j - v j| := by
    dsimp [a, b]
    rw [show (N : ℝ) * u j / 4 - (N : ℝ) * v j / 4 =
        (N : ℝ) / 4 * (u j - v j) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 4)]
  have hgrad : |psiGrad u j - psiGrad v j| =
      |qPrime a - qPrime b| / 4 := by
    dsimp [psiGrad, a, b]
    rw [← sub_div, abs_div]
    norm_num
  calc
    |psiGrad u j - psiGrad v j| = |qPrime a - qPrime b| / 4 := hgrad
    _ ≤ (6 * |a - b|) / 4 :=
      div_le_div_of_nonneg_right hq (by norm_num)
    _ = (3 * (N : ℝ) / 8) * |u j - v j| := by
      rw [hab]
      ring

/-- Global squared Euclidean Lipschitz estimate
`‖∇psi(u)-∇psi(v)‖² ≤ (9 N² / 64) ‖u-v‖²`. -/
theorem psiGrad_vecSq_sub_le {N : Nat} (u v : Fin N → ℝ) :
    WeaklyConvexLowerBound.Foundation.vecSq (psiGrad u - psiGrad v) ≤
      (9 * (N : ℝ) ^ 2 / 64) *
        WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
  unfold WeaklyConvexLowerBound.Foundation.vecSq
  change (∑ j, (psiGrad u j - psiGrad v j) ^ 2) ≤
    (9 * (N : ℝ) ^ 2 / 64) * ∑ j, (u j - v j) ^ 2
  calc
    (∑ j, (psiGrad u j - psiGrad v j) ^ 2) ≤
        ∑ j, (9 * (N : ℝ) ^ 2 / 64) * (u j - v j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hab := psiGrad_coord_abs_sub_le u v j
      have hc : (0 : ℝ) ≤ 3 * (N : ℝ) / 8 := by positivity
      have hsq : (psiGrad u j - psiGrad v j) ^ 2 ≤
          ((3 * (N : ℝ) / 8) * (u j - v j)) ^ 2 := by
        rw [sq_le_sq]
        simpa only [abs_mul, abs_of_nonneg hc] using hab
      calc
        (psiGrad u j - psiGrad v j) ^ 2 ≤
            ((3 * (N : ℝ) / 8) * (u j - v j)) ^ 2 := hsq
        _ = (9 * (N : ℝ) ^ 2 / 64) * (u j - v j) ^ 2 := by ring
    _ = (9 * (N : ℝ) ^ 2 / 64) * ∑ j, (u j - v j) ^ 2 := by
      rw [Finset.mul_sum]

/-- One-block form of the global squared Lipschitz estimate. -/
theorem blockSq_singleBlock_psiGrad_sub_le {M N : Nat} (m : Fin M)
    (u v : Fin N → ℝ) :
    blockSq (singleBlock m (psiGrad u - psiGrad v)) ≤
      (9 * (N : ℝ) ^ 2 / 64) *
        WeaklyConvexLowerBound.Foundation.vecSq (u - v) := by
  rw [blockSq_singleBlock]
  exact psiGrad_vecSq_sub_le u v

/-- An unrevealed zero coordinate makes no contribution to the gradient. -/
theorem psiGrad_eq_zero_of_coord_eq_zero {N : Nat} {u : Fin N → ℝ}
    (j : Fin N) (hu : u j = 0) : psiGrad u j = 0 := by
  simp [psiGrad, hu]

/-- Consequently, progress gradients preserve every coordinate prefix. -/
theorem psiGrad_prefixSupported {N k : Nat} {u : Fin N → ℝ}
    (hu : PrefixSupported k u) : PrefixSupported k (psiGrad u) := by
  intro j hj
  exact psiGrad_eq_zero_of_coord_eq_zero j (hu j hj)

end

end WeaklyConvexLowerBound

