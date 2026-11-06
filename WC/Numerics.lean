import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Numerical and combinatorial certificates

The indices below are zero based: the paper's level `(m-1)ℓ+n-1`
is therefore `m * ℓ + n`. These results certify the constants only;
they do not assume or assert existence of the hard function.
-/

namespace WC

/-- The stagger between successive blocks in the manuscript. -/
def stagger (N : ℕ) : ℕ := N / 4

/-- The zero-based diagonal level. -/
def diagonalLevel (N : ℕ) (i : ℕ × ℕ) : ℕ :=
  i.1 * stagger N + i.2

theorem stagger_pos {N : ℕ} (hN : 256 ≤ N) : 0 < stagger N := by
  unfold stagger
  omega

theorem five_stagger_ge {N : ℕ} (hN : 256 ≤ N) : N ≤ 5 * stagger N := by
  unfold stagger
  omega

theorem eight_stagger_ge {N : ℕ} (hN : 256 ≤ N) : N ≤ 8 * stagger N := by
  unfold stagger
  omega

/-- The exact integer horizon satisfies the paper's `T ≥ MN/16`. -/
theorem horizon_bound {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    M * N ≤ 16 * ((M - 1) * stagger N) := by
  have hm : M ≤ 2 * (M - 1) := by omega
  have hn := eight_stagger_ge hN
  nlinarith [Nat.mul_le_mul hm hn]

theorem horizon_bound_real {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    (M : ℝ) * N / 16 ≤ ((M - 1) * stagger N : ℕ) := by
  have h := horizon_bound hM hN
  have h' : (M : ℝ) * N ≤ 16 * (((M - 1) * stagger N : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith

/-- Two coordinates on one diagonal cannot be five blocks apart. -/
theorem diagonal_blocks_close {N m₁ m₂ n₁ n₂ : ℕ}
    (hN : 256 ≤ N) (hn₁ : n₁ < N) (hn₂ : n₂ < N)
    (hlevel : diagonalLevel N (m₁, n₁) = diagonalLevel N (m₂, n₂)) :
    m₁ < m₂ + 5 ∧ m₂ < m₁ + 5 := by
  have hwidth := five_stagger_ge hN
  dsimp [diagonalLevel] at hlevel
  constructor
  · by_contra h
    have hle : m₂ + 5 ≤ m₁ := by omega
    have hmul := Nat.mul_le_mul_right (stagger N) hle
    nlinarith
  · by_contra h
    have hle : m₁ + 5 ≤ m₂ := by omega
    have hmul := Nat.mul_le_mul_right (stagger N) hle
    nlinarith

/-- Each diagonal contains at most five coordinate directions. -/
theorem diagonal_width (M N r : ℕ) (hN : 256 ≤ N) :
    (Finset.univ.filter (fun i : Fin M × Fin N =>
      diagonalLevel N (i.1.val, i.2.val) = r)).card ≤ 5 := by
  classical
  let s := Finset.univ.filter (fun i : Fin M × Fin N =>
    diagonalLevel N (i.1.val, i.2.val) = r)
  let f : Fin M × Fin N → Fin 5 := fun i => ⟨i.1.val % 5, Nat.mod_lt _ (by omega)⟩
  have hcard : s.card ≤ (Finset.univ : Finset (Fin 5)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      simp
    · intro i hi j hj hij
      have hi' : diagonalLevel N (i.1.val, i.2.val) = r :=
        (Finset.mem_filter.mp hi).2
      have hj' : diagonalLevel N (j.1.val, j.2.val) = r :=
        (Finset.mem_filter.mp hj).2
      have hclose := diagonal_blocks_close hN i.2.isLt j.2.isLt (hi'.trans hj'.symm)
      have hmod : i.1.val % 5 = j.1.val % 5 := congrArg Fin.val hij
      have hm : i.1.val = j.1.val := by omega
      have hn : i.2.val = j.2.val := by
        dsimp [diagonalLevel] at hi' hj'
        rw [hm] at hi'
        omega
      exact Prod.ext (Fin.ext hm) (Fin.ext hn)
  simpa [s] using hcard

/-- Coordinates exposed before time `t`, corresponding to the paper's `I_{t-1}`. -/
def exposedIndices (M N t : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter (fun i => diagonalLevel N (i.1.val, i.2.val) < t)

theorem exposedIndices_zero (M N : ℕ) : exposedIndices M N 0 = ∅ := by
  simp [exposedIndices]

theorem exposedIndices_mono (M N : ℕ) {s t : ℕ} (hst : s ≤ t) :
    exposedIndices M N s ⊆ exposedIndices M N t := by
  intro i hi
  simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem exposedIndices_step (M N t : ℕ) :
    exposedIndices M N (t + 1) \ exposedIndices M N t =
      Finset.univ.filter (fun i : Fin M × Fin N =>
        diagonalLevel N (i.1.val, i.2.val) = t) := by
  ext i
  simp only [exposedIndices, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

theorem exposedIndices_step_card (M N t : ℕ) (hN : 256 ≤ N) :
    (exposedIndices M N (t + 1) \ exposedIndices M N t).card ≤ 5 := by
  rw [exposedIndices_step]
  exact diagonal_width M N t hN

/-- The entire last block remains hidden before the terminal time. -/
theorem last_block_unexposed {M N : ℕ} (hM : 0 < M) (n : Fin N) :
    (⟨M - 1, by omega⟩, n) ∉
      exposedIndices M N ((M - 1) * stagger N) := by
  simp [exposedIndices, diagonalLevel]

theorem terminal_indices_proper {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    exposedIndices M N ((M - 1) * stagger N) ≠ Finset.univ := by
  intro heq
  have hnot := last_block_unexposed hM (⟨0, hN⟩ : Fin N)
  rw [heq] at hnot
  simp at hnot

theorem normalized_gap_bound {M N γ : ℝ}
    (hM : 1 ≤ M) (hN : 0 < N) (hγ : γ < 1) :
    (2 * M + γ) / N ≤ 3 * M / N := by
  apply div_le_div_of_nonneg_right _ (le_of_lt hN)
  linarith

theorem source_dimension_bound {N B : ℝ} (hB : B ≤ 3 * N) :
    25 * N + 8 * B ≤ 49 * N := by
  linarith

/-- The strict numerical margin used after normalization. -/
theorem normalized_barrier_margin {N D : ℝ}
    (hN : 0 < N) (hD : 0 < D) (hDN : D ≤ 49 * N) :
    1 / (1024 * N) < 5 / (48 * D) := by
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 1024 * N)
    (by positivity : (0 : ℝ) < 48 * D)).2
  nlinarith

/-- Squared estimates suffice for the paper's strict gradient threshold. -/
theorem strict_barrier_from_square {N D g : ℝ}
    (hN : 0 < N) (hD : 0 < D) (hDN : D ≤ 49 * N)
    (hg : 0 ≤ g) (hbar : 5 / (48 * D) ≤ g ^ 2) :
    1 / (32 * Real.sqrt N) < g := by
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsq : (1 / (32 * Real.sqrt N)) ^ 2 = 1 / (1024 * N) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hN)]
    norm_num
  have hlt : (1 / (32 * Real.sqrt N)) ^ 2 < g ^ 2 := by
    rw [hsq]
    exact lt_of_lt_of_le (normalized_barrier_margin hN hD hDN) hbar
  have hnonneg : 0 ≤ 1 / (32 * Real.sqrt N) := by positivity
  nlinarith

/-- Integer selection of the within-block length in the scaling reduction. -/
theorem scaling_N_bounds {b : ℝ} (hb : (2 : ℝ) ^ 18 ≤ b) :
    256 ≤ ⌊b / 1024⌋₊ ∧
    b / 2048 ≤ (⌊b / 1024⌋₊ : ℝ) ∧
    (⌊b / 1024⌋₊ : ℝ) ≤ b / 1024 ∧
    b < 1024 * ((⌊b / 1024⌋₊ : ℝ) + 1) := by
  have hbpos : 0 ≤ b / 1024 := by positivity
  have hfloor := Nat.floor_le hbpos
  have hsucc := Nat.lt_floor_add_one (b / 1024)
  constructor
  · apply Nat.le_floor
    norm_num at hb ⊢
    linarith
  constructor
  · norm_num at hb
    linarith
  exact ⟨hfloor, by linarith⟩

/-- Integer selection of the number of blocks, with the floor loss explicit. -/
theorem scaling_M_bounds {r n : ℝ} (hrn : 12 ≤ r * n) :
    2 ≤ ⌊r * n / 3⌋₊ ∧
    r * n / 6 ≤ (⌊r * n / 3⌋₊ : ℝ) ∧
    3 * (⌊r * n / 3⌋₊ : ℝ) ≤ r * n := by
  have hx : 0 ≤ r * n / 3 := by linarith
  have hfloor := Nat.floor_le hx
  have hsucc := Nat.lt_floor_add_one (r * n / 3)
  constructor
  · apply Nat.le_floor
    norm_num
    linarith
  constructor <;> linarith

/-- The final polynomial loss in the large-parameter reduction. -/
theorem scaling_horizon_constant {b r n m t : ℝ}
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hn : b / 2048 ≤ n)
    (hm : r * n / 6 ≤ m) (hnpos : 0 ≤ n)
    (ht : m * n / 16 ≤ t) :
    b ^ 2 * r / (2 : ℝ) ^ 29 ≤ t := by
  have hmul : r * n ^ 2 / 96 ≤ m * n / 16 := by
    have := mul_le_mul_of_nonneg_right hm hnpos
    nlinarith
  have hsq : b ^ 2 / 2048 ^ 2 ≤ n ^ 2 := by
    have : 0 ≤ n - b / 2048 := by linarith
    nlinarith
  have hsqmul := mul_le_mul_of_nonneg_right hsq hr
  have htarget : b ^ 2 * r / (2 : ℝ) ^ 29 ≤ r * n ^ 2 / 96 := by
    norm_num at hsqmul ⊢
    nlinarith [mul_nonneg (sq_nonneg b) hr]
  exact htarget.trans (hmul.trans ht)

/-- An explicit universal constant for the two nested round counts in the upper bound. -/
theorem upper_call_count {b s : ℝ} (hb : 1 ≤ b) (hs : 1 ≤ s) :
    (⌈(2 : ℝ) ^ 14 * b⌉₊ : ℝ) * ((⌊32 * s⌋₊ : ℝ) + 1) ≤
      540705 * b * s := by
  have hbpos : 0 < b := by linarith
  have hspos : 0 < s := by linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ 14 * b by positivity)
  have hf := Nat.floor_le (show 0 ≤ 32 * s by positivity)
  have hc' : (⌈(2 : ℝ) ^ 14 * b⌉₊ : ℝ) ≤ 16385 * b := by
    norm_num at hc ⊢
    linarith
  have hf' : (⌊32 * s⌋₊ : ℝ) + 1 ≤ 33 * s := by linarith
  have hprod := mul_le_mul hc' hf' (by positivity) (by positivity : (0 : ℝ) ≤ 16385 * b)
  nlinarith

/-- A coarse logarithmic estimate sufficient for exponential admissibility. -/
theorem log_length_bound {n : ℝ} (hn : 256 ≤ n) :
    Real.log n ≤ n / 16 + 3 := by
  have hnpos : 0 < n := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < n / 16 by positivity)
  rw [Real.log_div (ne_of_gt hnpos) (by norm_num)] at hlog
  have hlog16 : Real.log 16 ≤ 4 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hpow := Real.log_pow (2 : ℝ) 4
    norm_num at hpow
    linarith
  linarith

/-- The scaling choices obey the upper admissibility restriction `M ≤ 2^(8N)`. -/
theorem scaling_exponential_admissibility {b r : ℝ}
    (hb : (2 : ℝ) ^ 18 ≤ b) (hrpos : 0 < r)
    (hr : r ≤ Real.exp (b / 200)) :
    ⌊r * (⌊b / 1024⌋₊ : ℝ) / 3⌋₊ ≤ 2 ^ (8 * ⌊b / 1024⌋₊) := by
  let N : ℕ := ⌊b / 1024⌋₊
  have hNnat : 256 ≤ N := (scaling_N_bounds hb).1
  have hN : (256 : ℝ) ≤ N := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < N := by linarith
  have hbN : b < 1028 * (N : ℝ) := by
    have h := (scaling_N_bounds hb).2.2.2
    change b < 1024 * ((N : ℝ) + 1) at h
    linarith
  have hlogN := log_length_bound hN
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hexponent : b / 200 + Real.log (N : ℝ) ≤
      (8 * (N : ℝ)) * Real.log 2 := by
    have hlogmul := mul_le_mul_of_nonneg_left hlog2
      (show (0 : ℝ) ≤ 8 * N by positivity)
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_add, Real.exp_log hNpos] at hexp
  have hexp_eq : Real.exp ((8 * (N : ℝ)) * Real.log 2) = (2 : ℝ) ^ (8 * N) := by
    have hcast : 8 * (N : ℝ) = ((8 * N : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexp_eq] at hexp
  have hprod : r * (N : ℝ) / 3 ≤ Real.exp (b / 200) * N := by
    have hmul := mul_le_mul_of_nonneg_right hr (le_of_lt hNpos)
    have hnonneg : 0 ≤ r * (N : ℝ) := by positivity
    linarith
  have hfloor := Nat.floor_le (show 0 ≤ r * (N : ℝ) / 3 by positivity)
  have hfinal : (⌊r * (N : ℝ) / 3⌋₊ : ℝ) ≤ (2 : ℝ) ^ (8 * N) :=
    hfloor.trans (hprod.trans hexp)
  exact_mod_cast hfinal

/-- All integer and polynomial certificates for the large-parameter scaling choice. -/
theorem scaling_integer_parameters {b r : ℝ}
    (hb : (2 : ℝ) ^ 18 ≤ b) (hrpos : 0 < r)
    (hs : (2 : ℝ) ^ 18 ≤ b * r)
    (hr : r ≤ Real.exp (b / 200)) :
    let N := ⌊b / 1024⌋₊
    let M := ⌊r * (N : ℝ) / 3⌋₊
    256 ≤ N ∧ 2 ≤ M ∧ M ≤ 2 ^ (8 * N) ∧
    3 * (M : ℝ) / N ≤ r ∧
    b ^ 2 * r / (2 : ℝ) ^ 29 ≤ (((M - 1) * stagger N : ℕ) : ℝ) := by
  dsimp only
  let N := ⌊b / 1024⌋₊
  let M := ⌊r * (N : ℝ) / 3⌋₊
  have hNbounds := scaling_N_bounds hb
  have hNnat : 256 ≤ N := hNbounds.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hrn : 12 ≤ r * (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hNbounds.2.1 (le_of_lt hrpos)
    norm_num at hs
    nlinarith
  have hMbounds := scaling_M_bounds hrn
  have hMnat : 2 ≤ M := hMbounds.1
  refine ⟨hNnat, hMnat, scaling_exponential_admissibility hb hrpos hr, ?_, ?_⟩
  · apply (div_le_iff₀ hNpos).2
    exact hMbounds.2.2
  · apply scaling_horizon_constant (by norm_num at hb; linarith)
      (le_of_lt hrpos) hNbounds.2.1 hMbounds.2.1 (le_of_lt hNpos)
    exact horizon_bound_real hMnat hNnat

/-- The sum of weighted proximal errors, before the averaging step.

`a` is the potential `ρ/4 * j*(j+1) * A_(j+1)`. The recurrence
is the scalar inequality obtained from projection and strong convexity.
-/
theorem weighted_error_telescope (L : ℕ) (E a : ℕ → ℝ) (C : ℝ)
    (ha0 : a 0 = 0) (haL : 0 ≤ a L)
    (hstep : ∀ k < L, ((k : ℝ) + 1) * E (k + 1) ≤ a k - a (k + 1) + C) :
    ∑ k ∈ Finset.range L, ((k : ℝ) + 1) * E (k + 1) ≤ C * L := by
  have htel : ∀ l ≤ L,
      ∑ k ∈ Finset.range l, ((k : ℝ) + 1) * E (k + 1) ≤
        a 0 - a l + C * l := by
    intro l
    induction l with
    | zero => intro hl; simp
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      have hnext := hstep l (by omega)
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have h := htel L le_rfl
  rw [ha0] at h
  linarith

/-- Averaging the preceding weighted sum gives the paper's inner-solver rate. -/
theorem weighted_average_error_bound {L : ℕ} {S C : ℝ}
    (hL : 0 < L) (hS : S ≤ C * L) :
    2 * S / ((L : ℝ) * (L + 1)) ≤ 2 * C / ((L : ℝ) + 1) := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  apply (div_le_div_iff₀ (by positivity : 0 < (L : ℝ) * (L + 1))
    (by positivity : 0 < (L : ℝ) + 1)).2
  have hmul := mul_le_mul_of_nonneg_right hS
    (show (0 : ℝ) ≤ (L : ℝ) + 1 by positivity)
  nlinarith

/-- The chosen number of inner iterations achieves the stated proximal tolerance. -/
theorem proximal_value_tolerance {G ε ρ L : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hiterations : (2 : ℝ) ^ 14 * G ^ 2 ≤ L * ε ^ 2) :
    18 * G ^ 2 / (ρ * (L + 1)) ≤ ε ^ 2 / (512 * ρ) := by
  apply (div_le_div_iff₀ (by positivity : 0 < ρ * (L + 1))
    (by positivity : 0 < 512 * ρ)).2
  have hnum : 18 * 512 * G ^ 2 ≤ ε ^ 2 * (L + 1) := by
    norm_num at hiterations
    nlinarith [sq_nonneg G, sq_nonneg ε]
  have := mul_le_mul_of_nonneg_right hnum (le_of_lt hρ)
  nlinarith

/-- Strong convexity turns the objective tolerance into the paper's distance tolerance. -/
theorem proximal_distance_tolerance {ε ρ d : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hvalue : ρ / 2 * d ^ 2 ≤ ε ^ 2 / (512 * ρ)) :
    d ≤ ε / (16 * ρ) := by
  have hmult := (le_div_iff₀ (by positivity : 0 < 512 * ρ)).1 hvalue
  apply (le_div_iff₀ (by positivity : 0 < 16 * ρ)).2
  have hnonneg : 0 ≤ d * (16 * ρ) := by positivity
  nlinarith [sq_nonneg (d * (16 * ρ) - ε)]

/-- The successful branch certifies a `5ε/8` bound at its center. -/
theorem certified_center_bound {ε ρ d₁ d₂ g : ℝ}
    (hρ : 0 < ρ) (h₁ : d₁ ≤ ε / (4 * ρ)) (h₂ : d₂ ≤ ε / (16 * ρ))
    (hg : g ≤ 2 * ρ * (d₁ + d₂)) : g ≤ 5 * ε / 8 := by
  have h₁' := (le_div_iff₀ (by positivity : 0 < 4 * ρ)).1 h₁
  have h₂' := (le_div_iff₀ (by positivity : 0 < 16 * ρ)).1 h₂
  nlinarith

/-- Every unsuccessful outer round decreases the original objective by the stated amount. -/
theorem unsuccessful_round_descent {ε ρ d decrease : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hd : ε / (4 * ρ) < d)
    (hdec : ρ * d ^ 2 - ε ^ 2 / (512 * ρ) ≤ decrease) :
    ε ^ 2 / (32 * ρ) < decrease := by
  have hdpos : 0 < d := lt_trans (by positivity) hd
  have hd' := (div_lt_iff₀ (by positivity : 0 < 4 * ρ)).1 hd
  have hsq : ε ^ 2 < (4 * ρ * d) ^ 2 := by nlinarith
  have hden : 0 < 512 * ρ := by positivity
  have hdec' := mul_le_mul_of_nonneg_right hdec (le_of_lt hden)
  have hne : ρ ≠ 0 := ne_of_gt hρ
  field_simp at hdec'
  apply (div_lt_iff₀ (by positivity : 0 < 32 * ρ)).2
  nlinarith

end WC
