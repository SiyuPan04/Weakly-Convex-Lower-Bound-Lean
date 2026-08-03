import WeaklyConvexLowerBound.TerminalAssembly
import WeaklyConvexLowerBound.TerminalFiltration
import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Concrete terminal Moreau-residual certificate

This module packages condition (C3) as a statement about *every* proximal
minimizer.  It therefore does not hide a choice of minimizer.  Once the
standard full-subdifferential formula is supplied, the terminal filtration,
weak-convex Fermat rule, and algebraic active-phase barrier form one closed
chain.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- Squared-norm formulation of a lower bound on every half-Moreau
residual at `y`. -/
def HalfMoreauResidualSqAbove {M N : Nat}
    (f : BlockVec M N → ℝ) (τsq : ℝ) (y : BlockVec M N) : Prop :=
  ∀ z, IsHalfProxPoint f y z → τsq < blockSq (halfProxResidual y z)

/-- Norm formulation, using the explicit Euclidean norm of the nested block
representation. -/
def HalfMoreauResidualAbove {M N : Nat}
    (f : BlockVec M N → ℝ) (τ : ℝ) (y : BlockVec M N) : Prop :=
  ∀ z, IsHalfProxPoint f y z →
    τ < Real.sqrt (blockSq (halfProxResidual y z))

/-- An explicit formula reply for every proximal residual rules out the
small-residual regime throughout the concrete terminal filtration. -/
theorem reachable_formula_residual_sq_above {M N : Nat}
    (hM : 0 < M) (hN : 0 < N) {f : BlockVec M N → ℝ}
    {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y)
    (hformula : ∀ z, IsHalfProxPoint f y z →
      HardFormulaReply z (halfProxResidual y z)) :
    HalfMoreauResidualSqAbove f (1 / (64 * (N : ℝ))) y := by
  intro z hz
  by_contra hnot
  have hsmall :
      blockSq (halfProxResidual y z) ≤ 1 / (64 * (N : ℝ)) :=
    le_of_not_gt hnot
  exact hardInstance_terminal_hardFormulaReply_contradiction
    hM hN (terminalVisible N) rfl
    (Reachable.hidden_lastBlock hM hy)
    (terminalVisible_indicator_le N) hsmall (hformula z hz)

/-- The honest semantic bridge version: weak convexity puts the proximal
residual in the standard full subdifferential, and a proved formula bridge
then supplies the explicit reply used by the terminal barrier. -/
theorem reachable_fullSubdiff_residual_sq_above_of_bridge {M N : Nat}
    (hM : 0 < M) (hN : 0 < N)
    {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y)
    (hweak : WeaklyConvex 1 (hardValue : BlockVec M N → ℝ))
    (hbridge : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        HardFormulaReply z g) :
    HalfMoreauResidualSqAbove
      (hardValue : BlockVec M N → ℝ) (1 / (64 * (N : ℝ))) y := by
  intro z hz
  by_contra hnot
  have hsmall : blockSq (halfProxResidual y z) ≤
      1 / (64 * (N : ℝ)) := le_of_not_gt hnot
  have hprogress := reachable_halfProx_small_terminal_progress
    hM hN hy hz hsmall
  have hR : 0 < activationNorm z := terminal_activation hM hN z hprogress
  have hq : QSubgradient (1 / 2 : ℝ)
      (hardValue : BlockVec M N → ℝ) z (halfProxResidual y z) :=
    hz.residual_qSubgradient_half_of_weaklyConvex hweak
  have hmem : halfProxResidual y z ∈
      fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z := by
    rw [mem_fullSubdiff_iff_qSubgradient]
    norm_num
    exact hq
  exact hardInstance_terminal_hardFormulaReply_contradiction
    hM hN (terminalVisible N) rfl
    (Reachable.hidden_lastBlock hM hy)
    (terminalVisible_indicator_le N) hsmall (hbridge z _ hR hmem)

theorem terminal_threshold_sq (N : Nat) (hN : 0 < N) :
    (1 / (8 * Real.sqrt (N : ℝ))) ^ 2 = 1 / (64 * (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNR).ne'
  rw [div_pow, mul_pow, Real.sq_sqrt hNR.le]
  norm_num

/-- Convert the squared certificate to the literal norm threshold appearing
in condition (C3). -/
theorem halfMoreauResidualAbove_of_sq {M N : Nat}
    (hN : 0 < N) {f : BlockVec M N → ℝ} {y : BlockVec M N}
    (h : HalfMoreauResidualSqAbove f (1 / (64 * (N : ℝ))) y) :
    HalfMoreauResidualAbove f (1 / (8 * Real.sqrt (N : ℝ))) y := by
  intro z hz
  rw [Real.lt_sqrt (by positivity : 0 ≤ 1 / (8 * Real.sqrt (N : ℝ)))]
  rw [terminal_threshold_sq N hN]
  exact h z hz

/-- Terminal condition (C3), still parametrized only by the exact semantic
formula theorem that the subsequent full-subdifferential module proves. -/
theorem reachable_fullSubdiff_residual_above_of_bridge {M N : Nat}
    (hM : 0 < M) (hN : 0 < N)
    {y : BlockVec M N}
    (hy : Reachable (relayDelay N) (horizon M N) y)
    (hweak : WeaklyConvex 1 (hardValue : BlockVec M N → ℝ))
    (hbridge : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        HardFormulaReply z g) :
    HalfMoreauResidualAbove (hardValue : BlockVec M N → ℝ)
      (1 / (8 * Real.sqrt (N : ℝ))) y :=
  halfMoreauResidualAbove_of_sq hN
    (reachable_fullSubdiff_residual_sq_above_of_bridge
      hM hN hy hweak hbridge)

end

end WeaklyConvexLowerBound

