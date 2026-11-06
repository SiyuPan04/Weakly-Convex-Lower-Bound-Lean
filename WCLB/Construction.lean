import WC.InitialGap
import WC.ChainWall
import WC.ChainBandBudget
import WC.LiftedChainBarrier
import WC.RobustLocality
import WC.MaskedSubdifferential
import WC.CoreFiltration

/-! Literal constants and the unscaled terminal certificate of the WCLB
manuscript. The construction itself is the same coupled majorant as WC. -/

noncomputable section
namespace WCLB
open WC

theorem initial_gap_le_five {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    GapBound (5 * (M : ℝ) / N) (chainMajorant (M := M) (N := N)) := by
  have hMpos : 0 < M := by omega
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply gapBound_iff_inf.mpr
  refine ⟨(chainMajorant_gapBound hMpos hN).bddBelow, ?_⟩
  rw [chainMajorant_gap hMpos hN]
  have hg := (initialGamma_bounds hMpos hNpos).2
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hh : (2 : ℝ) * (2 * (M : ℝ) + initialGamma M N) ≤ 5 * M := by linarith
  have hd := div_le_div_of_nonneg_right hh hNR.le
  convert hd using 1 <;> first | rfl | ring

theorem source_radius_bound {M N : ℕ} (hN : 256 ≤ N) :
    chainSourceRadius M N ≤ 128 * (M : ℝ) / (53 * (N : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := positiveScoreTerm_lipschitzConstant_le hN
  have hden : 0 < 2 - (1 / 4 + 3 / (2 * Real.sqrt (N : ℝ))) := by linarith
  unfold chainSourceRadius
  apply (div_le_div_iff₀ (mul_pos hNR hden) (by positivity : 0 < 53 * (N : ℝ))).mpr
  have hcoef : (212 : ℝ) ≤ 128 * (2 - (1 / 4 + 3 / (2 * Real.sqrt (N : ℝ)))) := by linarith
  have h := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (M : ℝ) * N by positivity)
  nlinarith

theorem source_radius_lt_three {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    {x y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 x) :
    ‖x - y‖ < 3 * (M : ℝ) / N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (chain_source_radius hN hy).trans_lt ((source_radius_bound hN).trans_lt ?_)
  apply (div_lt_div_iff₀ (by positivity : 0 < 53 * (N : ℝ)) hNR).mpr
  nlinarith [mul_pos hMR hNR]

theorem unscaled_terminal_barrier {M N : ℕ} (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (x : ChainSpace M N)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, x i ≤ robustTolerance M N) :
    1 / (10 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 9) chainMajorant) x‖ := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  let p := proximalPoint (9 / 2) (chainMajorant (M := M) (N := N)) x
  let v := (9 : ℝ) • (x - p)
  have hgrad : gradient (moreauEnvelope (1 / 9) chainMajorant) x = v := by
    have h := moreau_gradient_eq (by norm_num : (0 : ℝ) < 9 / 2)
      (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
      (chainMajorant_weaklyConvex hNpos) x
    norm_num at h
    exact h
  rw [hgrad]
  by_contra hfail
  have hvsmall : ‖v‖ ≤ 1 / (10 * Real.sqrt (N : ℝ)) := le_of_not_gt hfail
  have hvnorm : ‖v‖ = 9 * ‖x - p‖ := by simp [v, norm_smul]
  have hd : ‖x - p‖ ≤ 1 / Real.sqrt (N : ℝ) := by
    have hid : 1 / (10 * Real.sqrt (N : ℝ)) = (1 / 10 : ℝ) * (1 / Real.sqrt (N : ℝ)) := by ring
    rw [hid] at hvsmall
    nlinarith [norm_nonneg (x - p), show 0 ≤ 1 / Real.sqrt (N : ℝ) by positivity]
  have hp := proximalPoint_spec (by norm_num : (0 : ℝ) < 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos) x
  have hv : v ∈ subdifferential chainMajorant p := by
    have h := (hp.weakSubgradient (by norm_num) (chainMajorant_weaklyConvex hNpos)).frechet (by norm_num)
    norm_num at h
    exact h
  have hcoverage : chainSourceRadius M N ≤ (8 : ℝ) ^ (3 * N) * chainNearRadius N := by
    simpa only [chainNearRadius, div_eq_mul_inv, one_mul] using chain_source_radius_threeN_coverage hN hMmax
  have hfun : isometricLift (LinearIsometry.id : ChainSpace M N →ₗᵢ[ℝ] ChainSpace M N)
      chainMajorant = chainMajorant := by
    funext z
    exact congrArg chainMajorant (isometryProjection_map LinearIsometry.id z)
  have hb := lifted_chain_subgradient_norm_sq_lower hN
    (LinearIsometry.id : ChainSpace M N →ₗᵢ[ℝ] ChainSpace M N) x p v hcoverage s hcard
    (by intro i hi; simpa [isometryProjection] using (hsmall i hi).trans (robustTolerance_le_inv_N M hNpos))
    hd (by rw [hfun]; exact hv)
  have hb' : 1 / (49 * (N : ℝ)) ≤ ‖v‖ ^ 2 := by
    convert hb using 1 <;> push_cast <;> ring
  have hsq := (sq_le_sq₀ (norm_nonneg v) (show 0 ≤ 1 / (10 * Real.sqrt (N : ℝ)) by positivity)).mpr hvsmall
  have hid : (1 / (10 * Real.sqrt (N : ℝ))) ^ 2 = 1 / (100 * (N : ℝ)) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hNR.le]
    norm_num
  rw [hid] at hsq
  have hstrict : 1 / (100 * (N : ℝ)) < 1 / (49 * (N : ℝ)) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 100 * (N : ℝ)) (by positivity : 0 < 49 * (N : ℝ))).mpr
    nlinarith
  linarith

theorem terminal_diagonal_barrier {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (x : ChainSpace M N)
    (hidden : x ∈ diagonalTube M N ((M - 1) * stagger N)) :
    1 / (10 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 9) chainMajorant) x‖ := by
  apply unscaled_terminal_barrier hN hMmax x (terminalBlock (by omega : 0 < M))
    (by rw [terminalBlock_card])
  intro i hi
  have hn := terminalBlock_hidden (by omega : 0 < M) hi
  have hlevel : (M - 1) * stagger N ≤ diagonalLevel N (i.1.val, i.2.val) := by
    simpa only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hn
  exact (le_abs_self _).trans (hidden i hlevel).le

end WCLB
