import WeaklyConvexLowerBound.HardInstance
import WeaklyConvexLowerBound.TerminalBarrier
import WeaklyConvexLowerBound.HardFormulaReply

/-!
# Terminal certificate assembly for the concrete hard instance

This file connects the concrete terminal-activation lemma to the proximal
progress estimate and the algebraic subgradient barrier.  The only remaining
oracle-specific premise is the implication from positive activation to the
barrier for the particular reply `d`; `HardFormulaReply` later discharges that
premise for the manuscript's explicit formula oracle.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- Concrete assembly with the barrier exposed as one honest oracle premise. -/
theorem hardInstance_terminal_contradiction {M N : Nat}
    (hM : 0 < M) (hN : 0 < N)
    (visible : Finset (Fin N)) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y (lastBlock hM) j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ)))
    (hbarrier : 0 < activationNorm z →
      1 ≤ 16 * (N : ℝ) * blockSq d) : False :=
  terminal_activation_barrier_contradiction hN visible (lastBlock hM)
    hd hhidden hvisible_half hsmall
    (0 < activationNorm z)
    (terminal_activation hM hN z)
    hbarrier

/-- Concrete assembly through the finite formula-data interface. -/
theorem hardInstance_terminal_formula_contradiction {M N : Nat}
    (hM : 0 < M) (hN : 0 < N)
    (visible : Finset (Fin N)) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y (lastBlock hM) j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ)))
    (dataOfActive : 0 < activationNorm z → BarrierAlgebraData M N)
    (hreply : ∀ hp : 0 < activationNorm z, (dataOfActive hp).g = d) : False :=
  terminal_activation_barrierAlgebra_contradiction hN visible (lastBlock hM)
    hd hhidden hvisible_half hsmall
    (0 < activationNorm z)
    (terminal_activation hM hN z)
    dataOfActive hreply

/-- End-to-end terminal contradiction for the manuscript's explicit formula
reply.  The later analytic layer only has to show that the proximal residual
is such a reply and instantiate the terminal visible set. -/
theorem hardInstance_terminal_hardFormulaReply_contradiction {M N : Nat}
    (hM : 0 < M) (hN : 0 < N)
    (visible : Finset (Fin N)) {y z d : BlockVec M N}
    (hd : d = halfProxResidual y z)
    (hhidden : ∀ j, j ∉ visible → y (lastBlock hM) j = 0)
    (hvisible_half :
      (∑ j : Fin N, if j ∈ visible then (1 : ℝ) else 0) ≤ (N : ℝ) / 2)
    (hsmall : blockSq d ≤ 1 / (64 * (N : ℝ)))
    (reply : HardFormulaReply z d) : False :=
  hardInstance_terminal_contradiction hM hN visible hd hhidden hvisible_half
    hsmall (fun hR => hardFormulaReply_barrier hN hR reply)

end

end WeaklyConvexLowerBound

