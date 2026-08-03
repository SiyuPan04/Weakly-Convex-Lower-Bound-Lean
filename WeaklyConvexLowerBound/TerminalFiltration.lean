import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.Filtration
import WeaklyConvexLowerBound.HardInstance
import WeaklyConvexLowerBound.TerminalBarrier

/-!
# The concrete terminal filtration

This file discharges the finite-index bookkeeping which is left abstract in
`TerminalBarrier`.  At the terminal diagonal level, only the first `N / 2`
coordinates of the last block can be visible.  Consequently a half-proximal
residual with squared norm at most `1 / (64 N)` forces terminal progress below
the gate `27 / 32`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- The coordinates of the last block which occur strictly before the
terminal diagonal cutoff. -/
def terminalVisible (N : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun j => j.1 < N / 2

@[simp] theorem mem_terminalVisible {N : Nat} {j : Fin N} :
    j ∈ terminalVisible N ↔ j.1 < N / 2 := by
  simp [terminalVisible]

/-- There are at most `N / 2` visible coordinates in the terminal block. -/
theorem terminalVisible_card_le (N : Nat) :
    (terminalVisible N).card ≤ N / 2 := by
  classical
  calc
    (terminalVisible N).card ≤
        (Finset.range (N / 2)).card := by
      refine Finset.card_le_card_of_injOn
        (fun j : Fin N => j.1) ?_ ?_
      · intro j hj
        exact Finset.mem_range.2 (mem_terminalVisible.1 hj)
      · intro i hi j hj hij
        exact Fin.ext hij
    _ = N / 2 := by simp

/-- Real-valued indicator formulation expected by `TerminalBarrier`. -/
theorem terminalVisible_indicator_le (N : Nat) :
    (∑ j : Fin N, if j ∈ terminalVisible N then (1 : ℝ) else 0) ≤
      (N : ℝ) / 2 := by
  classical
  have hcard := terminalVisible_card_le N
  have hcardR : ((terminalVisible N).card : ℝ) ≤ (N / 2 : Nat) := by
    exact_mod_cast hcard
  have hdiv : ((N / 2 : Nat) : ℝ) ≤ (N : ℝ) / 2 := by
    have hn : 2 * (N / 2) ≤ N := by omega
    have hnR : (2 : ℝ) * ((N / 2 : Nat) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hn
    linarith
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  simpa using hcardR.trans hdiv

/-- A point in the terminal reachable region vanishes outside the first
`N / 2` coordinates of its last block. -/
theorem Reachable.hidden_lastBlock {M N : Nat} (hM : 0 < M)
    {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y) :
    ∀ j, j ∉ terminalVisible N → y (lastBlock hM) j = 0 := by
  intro j hj
  apply hy (lastBlock hM) j
  have hj' : N / 2 ≤ j.1 := by
    simpa only [mem_terminalVisible, not_lt] using hj
  simp only [horizon, level, lastBlock]
  omega

/-- The terminal visible set is also the block-prefix computed from the
diagonal filtration. -/
theorem terminalVisible_eq_visibleBlock {M N : Nat}
    (hM : 0 < M) (hN : 2 ≤ N) :
    terminalVisible N =
      visibleBlock N (relayDelay N) (horizon M N - 1) (lastBlock hM).1 := by
  classical
  ext j
  simp only [mem_terminalVisible, mem_visibleBlock]
  simp only [horizon, level, lastBlock]
  omega

/-- Concrete terminal progress estimate obtained directly from membership in
the reachable region. -/
theorem reachable_small_residual_terminal_progress {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) {y z d : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y)
    (hd : d = halfProxResidual y z)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ))) :
    psi (z (lastBlock hM)) < (27 : ℝ) / 32 := by
  exact psi_terminal_lt_three_quarters_gate hN (terminalVisible N)
    (lastBlock hM) hd (Reachable.hidden_lastBlock hM hy)
    (terminalVisible_indicator_le N) hsmall

/-- Version phrased using a selected half-proximal point. -/
theorem reachable_halfProx_small_terminal_progress {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) {f : BlockVec M N → ℝ}
    {y z : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y)
    (_hz : IsHalfProxPoint f y z)
    (hsmall : blockSq (halfProxResidual y z) ≤ 1 / (64 * (N : ℝ))) :
    psi (z (lastBlock hM)) < (27 : ℝ) / 32 := by
  exact reachable_small_residual_terminal_progress hM hN hy rfl hsmall

/-! ## The sharper proximal support supplied by weak convexity -/

private theorem blockSq_smul {M N : Nat} (a : ℝ) (v : BlockVec M N) :
    blockSq (a • v) = a ^ 2 * blockSq v := by
  unfold blockSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

private theorem blockDot_smul_right' {M N : Nat} (a : ℝ)
    (u v : BlockVec M N) :
    blockDot u (a • v) = a * blockDot u v := by
  rw [blockDot_comm, blockDot_smul_left, blockDot_comm]

private theorem blockSq_convex_combo_gap {M N : Nat} (t : ℝ)
    (x z : BlockVec M N) :
    (1 - t) * blockSq z + t * blockSq x -
        blockSq ((1 - t) • z + t • x) =
      t * (1 - t) * blockSq (x - z) := by
  unfold blockSq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (1 - t) * (∑ m, ∑ j, z m j ^ 2) +
          t * (∑ m, ∑ j, x m j ^ 2) -
          ∑ m, ∑ j, ((1 - t) * z m j + t * x m j) ^ 2 =
        ∑ m, ∑ j, ((1 - t) * z m j ^ 2 + t * x m j ^ 2 -
          ((1 - t) * z m j + t * x m j) ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = ∑ m, ∑ j, t * (1 - t) * (x m j - z m j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = t * (1 - t) * (∑ m, ∑ j, (x m j - z m j) ^ 2) := by
      simp only [Finset.mul_sum]

private theorem convex_combo_eq_base_add {M N : Nat} (t : ℝ)
    (x z : BlockVec M N) :
    (1 - t) • z + t • x = z + t • (x - z) := by
  ext m j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem blockSq_base_add {M N : Nat} (t : ℝ)
    (x z y : BlockVec M N) :
    blockSq (z + t • (x - z) - y) =
      blockSq (z - y) + 2 * t * blockDot (x - z) (z - y) +
        t ^ 2 * blockSq (x - z) := by
  have hthree := blockSq_three_point (z + t • (x - z)) y z
  have hdiff : z + t • (x - z) - z = t • (x - z) := by
    ext m j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hthree, hdiff, blockSq_smul, blockDot_smul_left]
  ring

private theorem halfProxResidual_dot {M N : Nat}
    (x y z : BlockVec M N) :
    blockDot (halfProxResidual y z) (x - z) =
      -2 * blockDot (x - z) (z - y) := by
  unfold halfProxResidual
  rw [blockDot_smul_left, blockDot_comm (y - z) (x - z)]
  have hneg : y - z = -(z - y) := by
    ext m j
    simp
  rw [hneg]
  unfold blockDot
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

/-- A positive interpolation parameter gives the exact weak-convex support
inequality up to an error `t / 2 * ‖x-z‖²`. -/
private theorem weaklyConvex_halfProx_approx_support {M N : Nat}
    {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hweak : WeaklyConvex 1 f) (hz : IsHalfProxPoint f y z)
    (x : BlockVec M N) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    f z + blockDot (halfProxResidual y z) (x - z) -
        (1 / 2 : ℝ) * blockSq (x - z) ≤
      f x + t / 2 * blockSq (x - z) := by
  let w : BlockVec M N := (1 - t) • z + t • x
  have hconv := hweak.2 (Set.mem_univ z) (Set.mem_univ x)
    (sub_nonneg.2 ht1.le) ht0.le (by ring : (1 - t) + t = 1)
  have hgap := blockSq_convex_combo_gap t x z
  have hfw :
      f w ≤ (1 - t) * f z + t * f x +
        t * (1 - t) / 2 * blockSq (x - z) := by
    dsimp [w] at hconv
    dsimp [w]
    nlinarith
  have hmin := hz w
  have hnorm :
      blockSq (w - y) = blockSq (z - y) +
        2 * t * blockDot (x - z) (z - y) +
          t ^ 2 * blockSq (x - z) := by
    dsimp [w]
    rw [convex_combo_eq_base_add]
    exact blockSq_base_add t x z y
  have hdot := halfProxResidual_dot x y z
  nlinarith [blockSq_nonneg (x - z)]

/-- For a `1`-weakly convex function, half-proximal optimality sharpens the
pure-minimality coefficient `1` to the exact coefficient `1/2`.  This is the
quadratic-support form of
`2 (y-z) ∈ ∂f(z)` used in the manuscript. -/
theorem IsHalfProxPoint.residual_qSubgradient_half_of_weaklyConvex
    {M N : Nat} {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) (hweak : WeaklyConvex 1 f) :
    QSubgradient (1 / 2 : ℝ) f z (halfProxResidual y z) := by
  intro x
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  let B : ℝ := blockSq (x - z)
  let D : ℝ := B + ε + 1
  let t : ℝ := ε / D
  have hB : 0 ≤ B := blockSq_nonneg _
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have ht0 : 0 < t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hD]
    dsimp [D]
    linarith
  have happ := weaklyConvex_halfProx_approx_support hweak hz x ht0 ht1
  have hrewrite : t / 2 * B = (ε * B / 2) / D := by
    dsimp [t]
    field_simp [ne_of_gt hD]
  have herr : t / 2 * B ≤ ε := by
    rw [hrewrite, div_le_iff₀ hD]
    dsimp [D]
    nlinarith
  dsimp [B] at herr
  exact happ.trans (by linarith)

/-- Set-membership formulation of the preceding exact support theorem. -/
theorem IsHalfProxPoint.residual_mem_qSubdiff_half_of_weaklyConvex
    {M N : Nat} {f : BlockVec M N → ℝ} {y z : BlockVec M N}
    (hz : IsHalfProxPoint f y z) (hweak : WeaklyConvex 1 f) :
    halfProxResidual y z ∈ qSubdiff (1 / 2 : ℝ) f z :=
  hz.residual_qSubgradient_half_of_weaklyConvex hweak

end

end WeaklyConvexLowerBound

