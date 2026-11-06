import WC.ChainWall
import WC.LiftedChainBarrier
import WC.RadialSubgradient
import WC.RadialNoncancellation

/-! The actual Moreau gradient barrier for the final embedded radial wall. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [FiniteDimensional ℝ E]

theorem chainRadialWall_moreau_barrier {M N B : ℕ} (hN : 256 ≤ N)
    {R Δ : ℝ} (hR : 1 ≤ R) (hgapRaw : GapBound Δ (chainMajorant (M := M) (N := N)))
    (hcoverage : chainSourceRadius M N ≤ (8 : ℝ) ^ B * chainNearRadius N)
    (hmargin : 96 * chainRadialConstant M N * (25 * (N : ℝ) + 8 * (B : ℝ)) ≤ R - Δ / 3)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, isometryProjection U x i ≤ 1 / (N : ℝ)) :
    (15 / 16 : ℝ) / ((25 * (N : ℝ) + 8 * (B : ℝ))) ≤
      ‖gradient (moreauEnvelope (1 / 9) (radialWall (isometricLift U chainMajorant) R)) x‖ ^ 2 := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  let f : E → ℝ := isometricLift U chainMajorant
  let D : ℝ := (25 * (N : ℝ) + 8 * (B : ℝ))
  let k : ℝ := 1 / D
  let p := proximalPoint (9 / 2) (radialWall (isometricLift U chainMajorant) R) x
  let v : E := (9 : ℝ) • (x - p)
  have hD : 0 < D := by dsimp [D]; positivity
  have hk : 0 < k := div_pos (by norm_num) hD
  have hkmax : k ≤ 1 / 16 := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    have h256 : (256 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hLip : GloballyLipschitz 2 f := isometricLift_lipschitz U (by norm_num) (chainMajorant_lipschitz hNpos)
  have hWC : WeaklyConvex (9 / 2 : ℝ) f :=
    isometricLift_weaklyConvex U (by norm_num) (chainMajorant_weaklyConvex hNpos)
  have hadm : Admissible 3 (9 / 2) Δ (radialWall (isometricLift U chainMajorant) R) :=
    ⟨radialWall_weaklyConvex (by norm_num) hWC R, radialWall_lipschitz hLip R,
      radialWall_gapBound (isometricLift_gap U hgapRaw) (by linarith)⟩
  have hgrad : gradient (moreauEnvelope (1 / 9) (radialWall (isometricLift U chainMajorant) R)) x = v := by
    have hg := moreau_gradient_eq (by norm_num : (0 : ℝ) < 9 / 2)
      (by norm_num : (0 : ℝ) ≤ 3) hadm.lipschitz hadm.weaklyConvex x
    norm_num at hg
    exact hg
  rw [hgrad]
  rw [show (15 / 16 : ℝ) / ((25 * (N : ℝ) + 8 * (B : ℝ))) = (15 / 16 : ℝ) * k by dsimp [k, D]; ring]
  by_contra hfail
  have hsmallv : ‖v‖ ^ 2 < (15 / 16 : ℝ) * k := lt_of_not_ge hfail
  have hcompare : (15 / 16 : ℝ) * k ≤ (1 / Real.sqrt (N : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hNR.le]
    have hND : (N : ℝ) ≤ D := by
      dsimp [D]
      have hB : (0 : ℝ) ≤ B := by positivity
      linarith
    have hkn : k ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNR hND
    nlinarith
  have hvbound : ‖v‖ ≤ 1 / Real.sqrt (N : ℝ) := by
    nlinarith [norm_nonneg v, show 0 ≤ 1 / Real.sqrt (N : ℝ) by positivity]
  have hvnorm : ‖v‖ = 9 * ‖x - p‖ := by simp [v, norm_smul]
  have hdist : ‖x - p‖ ≤ 1 / Real.sqrt (N : ℝ) := by
    nlinarith [norm_nonneg (x - p)]
  have hchain (h : E) (hh : h ∈ subdifferential f p) : k ≤ ‖h‖ ^ 2 := by
    have h := lifted_chain_subgradient_norm_sq_lower hN U x p h hcoverage s hcard hsmall hdist hh
    exact h
  have hp := proximalPoint_spec (by norm_num : (0 : ℝ) < 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 3) hadm.lipschitz x
  have hv : v ∈ subdifferential (radialWall f R) p := by
    have hh := (hp.weakSubgradient (by norm_num) hadm.weaklyConvex).frechet (by norm_num)
    norm_num at hh
    exact hh
  rcases radialWall_subgradient_cases (by norm_num : (0 : ℝ) ≤ 9 / 2)
      (by linarith : 0 < R)
      hLip hWC hv with hchainv | ⟨w, h, hw0, hw1, hh, hactive, hpne, hrep⟩
  · have hb := hchain v hchainv
    nlinarith
  · have hgap : GapBound Δ f := isometricLift_gap U hgapRaw
    have hrad := radialBranch_active_norm_lower hgap hactive
    have hrad' : 96 * chainRadialConstant M N * D ≤ ‖p‖ := by
      change 96 * chainRadialConstant M N * (25 * (N : ℝ) + 8 * (B : ℝ)) ≤ ‖p‖
      linarith
    have hr : 0 < ‖p‖ := norm_pos_iff.mpr hpne
    have hratio : chainRadialConstant M N / ‖p‖ ≤ k / 96 := by
      have hid : k / 96 = 1 / (96 * D) := by dsimp [k]; ring
      rw [hid]
      apply (div_le_div_iff₀ hr (by positivity : 0 < 96 * D)).mpr
      nlinarith
    have hi := lifted_chain_radial_inner_lower hN U p h hh
    have hiscale := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
    have hie : -k / 96 ≤ inner ℝ h (‖p‖⁻¹ • p) := by
      rw [real_inner_smul_right]
      have hid : ‖p‖⁻¹ * (-chainRadialConstant M N) = -(chainRadialConstant M N / ‖p‖) := by ring
      rw [hid] at hiscale
      linarith
    have he : ‖‖p‖⁻¹ • p‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hbound := radial_vector_margin hk.le hkmax hw0 hw1 he (hchain h hh) hie
    rw [← hrep] at hbound
    nlinarith

end WC

