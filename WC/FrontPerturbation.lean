import WC.LocalityPerturbation
import WC.ChainSources

/-! An actual majorant source cannot have the front-curvature local path formulas. -/

noncomputable section
namespace WC
open scoped BigOperators

theorem front_objective_gain_of_local_formulas {M N : ℕ} (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (curve : ℝ → ChainSpace M N) {S R C ε : ℝ}
    (hS : 0 < S) (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε)
    (hSdef : ‖positiveCoupledScores y‖ = S) (hRdef : ‖x - y‖ = R)
    (hfront : 64 * S < (N : ℝ) * R)
    (hprogress : ∀ t, 0 < t → t < ε →
      (∑ m, blockProgress (coupledBlock (curve t) m)) = ∑ m, blockProgress (coupledBlock y m))
    (hscore : ∀ t, 0 < t → t < ε → ‖positiveCoupledScores (curve t)‖ ^ 2 =
      S ^ 2 + ((N : ℝ) ^ 2 / 64) * C * t ^ 2)
    (hdistance : ∀ t, 0 < t → t < ε → ‖x - curve t‖ ^ 2 = R ^ 2 + C * t ^ 2) : False := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨t, ht, htε, hgain⟩ := exists_front_objective_gain hNreal hS hR hC hfront hε
  have hsqrt : ‖positiveCoupledScores (curve t)‖ =
      Real.sqrt (S ^ 2 + ((N : ℝ) ^ 2 / 64) * C * t ^ 2) := by
    rw [← hscore t ht htε, Real.sqrt_sq (norm_nonneg _)]
  have hdsqrt : ‖x - curve t‖ = Real.sqrt (R ^ 2 + C * t ^ 2) := by
    rw [← hdistance t ht htε, Real.sqrt_sq (norm_nonneg _)]
  have hpayoff : sourcePayoff coupledFunction 2 x y < sourcePayoff coupledFunction 2 x (curve t) := by
    unfold sourcePayoff coupledFunction
    rw [hprogress t ht htε, hSdef, hRdef, hsqrt, hdsqrt]
    nlinarith
  have hupper := payoff_le_majorant (chainMajorant_finite hN) x (curve t)
  change sourcePayoff coupledFunction 2 x y = lipschitzMajorant coupledFunction 2 x at hy
  linarith

theorem source_forbids_front_local_formulas {M N : ℕ} (hN : 0 < N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x)
    (curve : ℝ → ChainSpace M N) {S R C : ℝ}
    (hS : 0 < S) (hR : 0 < R) (hC : 0 < C)
    (hSdef : ‖positiveCoupledScores y‖ = S) (hRdef : ‖x - y‖ = R)
    (hfront : 64 * S < (N : ℝ) * R)
    (hlocal : ∃ ε > 0, ∀ t, 0 < t → t < ε →
      (∑ m, blockProgress (coupledBlock (curve t) m)) = (∑ m, blockProgress (coupledBlock y m)) ∧
      ‖positiveCoupledScores (curve t)‖ ^ 2 = S ^ 2 + ((N : ℝ) ^ 2 / 64) * C * t ^ 2 ∧
      ‖x - curve t‖ ^ 2 = R ^ 2 + C * t ^ 2) : False := by
  obtain ⟨ε, hε, hlocal⟩ := hlocal
  exact front_objective_gain_of_local_formulas hN hy curve hS hR hC hε hSdef hRdef hfront
    (fun t ht hte => (hlocal t ht hte).1) (fun t ht hte => (hlocal t ht hte).2.1)
    (fun t ht hte => (hlocal t ht hte).2.2)

end WC
