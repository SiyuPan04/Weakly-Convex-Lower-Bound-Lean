import WeaklyConvexLowerBound.Progress
import WeaklyConvexLowerBound.QuadraticSubgradient
import WeaklyConvexLowerBound.BarrierAlgebra

/-!
# Terminal-layer obstruction

This file formalizes the numerical core of TeX lines 2051--2094.  It keeps
the three logically separate ingredients explicit:

* a filtration statement says which terminal coordinates of the query are
  zero, together with the elementary fact that the visible coordinates have
  total mass at most `N / 2`;
* the proximal identity `d = 2 (y - z)` and the cubic estimate on `q` force
  `psi (z m) < 27 / 32` when `blockSq d <= 1 / (64 N)`;
* terminal activation and the algebraic subgradient barrier then contradict
  that same small-residual bound.

Activation is represented below by an arbitrary proposition `P`.  Thus the
assembly theorem cannot use its conclusion circularly: it requires one map
from the strict progress inequality to `P`, and a separate map from `P` to
the barrier inequality (or to `BarrierAlgebraData`).
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-! ## The hidden half of the terminal block -/

/-- A single block has no more squared energy than the complete block
vector. -/
theorem block_energy_le_blockSq {M N : Nat} (d : BlockVec M N) (m : Fin M) :
    (∑ j, (d m j) ^ 2) ≤ blockSq d := by
  unfold blockSq
  exact Finset.single_le_sum
    (fun m' _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (d m' j))
    (Finset.mem_univ m)

/-- On a query coordinate which is zero, the half-proximal residual identity
is exactly `z = -d/2`. -/
theorem hidden_coordinate_of_halfProxResidual {M N : Nat}
    {y z d : BlockVec M N} (m : Fin M) (j : Fin N)
    (hd : d = halfProxResidual y z) (hy : y m j = 0) :
    z m j = -(d m j) / 2 := by
  have hcoord := congrFun (congrFun hd m) j
  simp only [halfProxResidual, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hcoord
  rw [hy] at hcoord
  linarith

private theorem max_zero_sq_le_sq (t : ℝ) : (max t 0) ^ 2 ≤ t ^ 2 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
  · rw [max_eq_right (le_of_not_ge ht)]
    simpa using sq_nonneg t

/-- The contribution of one hidden terminal coordinate is controlled by the
squared proximal residual on that coordinate. -/
theorem hidden_coordinate_q_le {M N : Nat} {y z d : BlockVec M N}
    (m : Fin M) (j : Fin N) (hd : d = halfProxResidual y z)
    (hy : y m j = 0) :
    q ((N : ℝ) * z m j / 4) ≤
      (3 * (N : ℝ) ^ 2 / 64) * (d m j) ^ 2 := by
  have hz := hidden_coordinate_of_halfProxResidual m j hd hy
  have harg : (N : ℝ) * z m j / 4 = -((N : ℝ) * d m j / 8) := by
    rw [hz]
    ring
  calc
    q ((N : ℝ) * z m j / 4) =
        q (-((N : ℝ) * d m j / 8)) := by rw [harg]
    _ ≤ 3 * (max (-((N : ℝ) * d m j / 8)) 0) ^ 2 :=
      q_le_three_mul_posPart_sq _
    _ ≤ 3 * (-((N : ℝ) * d m j / 8)) ^ 2 :=
      mul_le_mul_of_nonneg_left (max_zero_sq_le_sq _) (by norm_num)
    _ = (3 * (N : ℝ) ^ 2 / 64) * (d m j) ^ 2 := by ring

/-- An abstract visible-coordinate set for the terminal block.  Outside this
set the query is zero.  The final hypothesis is precisely the elementary
cardinality obligation supplied by the paper's terminal filtration: at most
half of the `N` coordinates are visible.

Keeping that obligation explicit makes this lemma reusable and prevents the
analytic proximal calculation from depending on any indexing convention. -/
theorem psi_terminal_le_half_add_residual {M N : Nat} (hN : 0 < N)
    (visible : Finset (Fin N)) (m : Fin M) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y m j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2) :
    psi (z m) ≤ (1 : ℝ) / 2 + (3 * (N : ℝ) / 64) * blockSq d := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let C : ℝ := 3 * (N : ℝ) ^ 2 / 64
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hterm (j : Fin N) :
      q ((N : ℝ) * z m j / 4) ≤
        (if j ∈ visible then (1 : ℝ) else 0) + C * (d m j) ^ 2 := by
    by_cases hj : j ∈ visible
    · simp only [hj, if_pos]
      have hq := q_le_one ((N : ℝ) * z m j / 4)
      have hnonneg : 0 ≤ C * (d m j) ^ 2 :=
        mul_nonneg hC (sq_nonneg _)
      linarith
    · simp only [hj, if_neg, zero_add]
      simpa [C] using hidden_coordinate_q_le m j hd (hhidden j hj)
  have hsum :
      (∑ j, q ((N : ℝ) * z m j / 4)) ≤
        ∑ j, ((if j ∈ visible then (1 : ℝ) else 0) + C * (d m j) ^ 2) :=
    Finset.sum_le_sum fun j _ ↦ hterm j
  have hblock := block_energy_le_blockSq d m
  unfold psi
  rw [div_le_iff₀ hNR]
  calc
    (∑ j, q ((N : ℝ) * z m j / 4)) ≤
        ∑ j, ((if j ∈ visible then (1 : ℝ) else 0) + C * (d m j) ^ 2) :=
      hsum
    _ = (∑ j, if j ∈ visible then (1 : ℝ) else 0) +
        C * ∑ j, (d m j) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (N : ℝ) / 2 + C * blockSq d := by
      exact add_le_add hvisible_half (mul_le_mul_of_nonneg_left hblock hC)
    _ = ((1 : ℝ) / 2 + (3 * (N : ℝ) / 64) * blockSq d) * (N : ℝ) := by
      dsimp [C]
      ring

/-- The exact constants from the manuscript imply strict terminal
nonactivation: `1/2 + 3/4096 < 27/32`. -/
theorem psi_terminal_lt_three_quarters_gate {M N : Nat} (hN : 0 < N)
    (visible : Finset (Fin N)) (m : Fin M) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y m j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ))) :
    psi (z m) < (27 : ℝ) / 32 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpsi := psi_terminal_le_half_add_residual hN visible m hd hhidden hvisible_half
  have hcoef : 0 ≤ (3 * (N : ℝ) / 64) := by positivity
  calc
    psi (z m) ≤ (1 : ℝ) / 2 + (3 * (N : ℝ) / 64) * blockSq d := hpsi
    _ ≤ (1 : ℝ) / 2 +
        (3 * (N : ℝ) / 64) * (1 / (64 * (N : ℝ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hcoef)
    _ = (1 : ℝ) / 2 + 3 / 4096 := by
      field_simp [ne_of_gt hNR]
      <;> ring
    _ < (27 : ℝ) / 32 := by norm_num

/-! ## The numerical contradiction -/

/-- The barrier lower bound and the proposed small residual cannot both
hold.  This is the constant-only final line of the terminal proof. -/
theorem barrier_small_residual_contradiction {M N : Nat} (hN : 0 < N)
    {d : BlockVec M N}
    (hbarrier : 1 ≤ 16 * (N : ℝ) * blockSq d)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ))) : False := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hscale : 0 ≤ 16 * (N : ℝ) := by positivity
  have hupper : 16 * (N : ℝ) * blockSq d ≤ (1 : ℝ) / 4 := by
    calc
      16 * (N : ℝ) * blockSq d ≤
          16 * (N : ℝ) * (1 / (64 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hsmall hscale
      _ = (1 : ℝ) / 4 := by
        field_simp [ne_of_gt hNR]
        <;> ring
  linarith

/-- Direct specialization of the preceding contradiction to the explicit
finite-sum barrier proved in `BarrierAlgebra`. -/
theorem barrierAlgebra_excludes_small_residual {M N : Nat} (hN : 0 < N)
    (data : BarrierAlgebraData M N)
    (hsmall : blockSq data.g ≤ 1 / (64 * (N : ℝ))) : False :=
  barrier_small_residual_contradiction hN (barrier_algebra hN data) hsmall

/-- Honest abstract assembly of the terminal proof.  `P` is the phase
activation event.  The two arrows are separate premises: progress below the
gate activates a phase, and an active phase supplies the barrier. -/
theorem terminal_activation_barrier_contradiction {M N : Nat} (hN : 0 < N)
    (visible : Finset (Fin N)) (m : Fin M) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y m j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ)))
    (P : Prop)
    (hactivate : psi (z m) < (27 : ℝ) / 32 → P)
    (hbarrier : P → 1 ≤ 16 * (N : ℝ) * blockSq d) : False := by
  have hprogress :=
    psi_terminal_lt_three_quarters_gate hN visible m hd hhidden hvisible_half hsmall
  exact barrier_small_residual_contradiction hN (hbarrier (hactivate hprogress)) hsmall

/-- Assembly using the concrete `BarrierAlgebraData` interface.  An active
phase must construct the data and identify its oracle reply with the
proximal residual. -/
theorem terminal_activation_barrierAlgebra_contradiction {M N : Nat}
    (hN : 0 < N) (visible : Finset (Fin N)) (m : Fin M)
    {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y m j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ)))
    (P : Prop)
    (hactivate : psi (z m) < (27 : ℝ) / 32 → P)
    (dataOfActive : P → BarrierAlgebraData M N)
    (hreply : ∀ hp : P, (dataOfActive hp).g = d) : False := by
  have hprogress :=
    psi_terminal_lt_three_quarters_gate hN visible m hd hhidden hvisible_half hsmall
  have hp : P := hactivate hprogress
  have hbarrier := barrier_algebra hN (dataOfActive hp)
  rw [hreply hp] at hbarrier
  exact barrier_small_residual_contradiction hN hbarrier hsmall

end

end WeaklyConvexLowerBound

