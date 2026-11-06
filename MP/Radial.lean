import MP.Construction
import WC.GeneralRadialBarrier
import WC.GeneralMoreauScaling
import WC.LowerReduction
import WC.PrefixOracleLocality

/-! The MP submission's prescribed radius and exact normalized radial
objective, including its own Moreau gradient and complete oracle. -/

noncomputable section
namespace MP
open WC Filter Topology

def radialRadius (M N : ℕ) : ℝ := (2 : ℝ) ^ 18 * ((M : ℝ) + Real.sqrt ((M * N : ℕ) : ℝ))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def radialObjectiveAt {M N : ℕ} (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) : ℝ :=
  max ((1 / 2 : ℝ) * chainMajorant ((2 / 3 : ℝ) • isometryProjection U x))
    ((1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖x‖ - R)

def radialObjective {M N : ℕ} (U : ChainSpace M N →ₗᵢ[ℝ] E) : E → ℝ :=
  radialObjectiveAt (radialRadius M N) U

theorem radialObjectiveAt_eq_scaledWall {M N : ℕ} (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    radialObjectiveAt R U = scaleFunction (1 / 2) (2 / 3)
      (radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * R)) := by
  funext x
  simp only [radialObjectiveAt, scaleFunction, radialWall, radialBranch, isometricLift,
    map_smul, map_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

theorem radialRadius_pos {M N : ℕ} (hM : 0 < M) : 0 < radialRadius M N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  unfold radialRadius
  positivity

theorem scaled_radius_ge_one {M N : ℕ} (hM : 2 ≤ M) : 1 ≤ (2 / 3 : ℝ) * radialRadius M N := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold radialRadius
  rw [show (2 : ℝ) ^ 18 = 262144 by norm_num]
  nlinarith [Real.sqrt_nonneg ((M * N : ℕ) : ℝ)]

theorem radial_radius_margin {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    96 * chainRadialConstant M N * (49 * (N : ℝ)) ≤
      (2 / 3 : ℝ) * radialRadius M N - (5 * (M : ℝ) / N) / 3 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm : (0 : ℝ) ≤ M := by positivity
  have hs : 0 ≤ Real.sqrt ((M * N : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hb := source_radius_bound (M := M) hN
  have hrad : chainSourceRadius M N * N ≤ 3 * M := by
    have h := (le_div_iff₀ (by positivity : 0 < 53 * (N : ℝ))).mp hb
    nlinarith [mul_nonneg hm hNR.le]
  have hc : chainRadialConstant M N * N ≤ 18 * Real.sqrt ((M * N : ℕ) : ℝ) + 6 * M := by
    have hid : chainRadialConstant M N * N =
        18 * Real.sqrt ((M * N : ℕ) : ℝ) + 2 * (chainSourceRadius M N * N) := by
      unfold chainRadialConstant
      field_simp
    rw [hid]
    linarith
  have hgap : 5 * (M : ℝ) / N ≤ 5 * M := by
    apply div_le_self (by positivity) hn
  unfold radialRadius
  rw [show (2 : ℝ) ^ 18 = 262144 by norm_num]
  nlinarith

theorem radialObjectiveAt_admissible {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    {R : ℝ} (hR : 0 ≤ R) (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (radialObjectiveAt R U) := by
  have hNpos : 0 < N := by omega
  have hl := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hw := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  have hbase : Admissible 3 (9 / 2) (5 * (M : ℝ) / N)
      (radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * R)) :=
    ⟨radialWall_weaklyConvex (by norm_num) hw _, radialWall_lipschitz hl _,
      radialWall_gapBound (isometricLift_gap U (initial_gap_le_five hM hN)) (by positivity)⟩
  have hh := admissible_scale (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hbase
  norm_num at hh
  rw [radialObjectiveAt_eq_scaledWall]
  exact ⟨hh.weaklyConvex, hh.lipschitz, hh.gap.mono (by
    have hn : (0 : ℝ) ≤ N := by positivity
    have hm : (0 : ℝ) ≤ M := by positivity
    have h : 0 ≤ (M : ℝ) / N := div_nonneg hm hn
    calc
      (1 / 2 : ℝ) * (5 * (M : ℝ) / N) = (5 / 2 : ℝ) * ((M : ℝ) / N) := by ring
      _ ≤ 3 * ((M : ℝ) / N) := by nlinarith
      _ = _ := by ring)⟩

theorem radial_admissible {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (radialObjective U) :=
  radialObjectiveAt_admissible hM hN (radialRadius_pos (by omega)).le U

variable [ProperSpace E]

theorem radialObjectiveAt_moreau_gradient {M N : ℕ} (hN : 256 ≤ N)
    (R : ℝ) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) :
    gradient (moreauEnvelope (1 / 2) (radialObjectiveAt R U)) x =
      (1 / 3 : ℝ) • gradient (moreauEnvelope (1 / 9)
        (radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * R))) ((2 / 3 : ℝ) • x) := by
  have hNpos : 0 < N := by omega
  have hl := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hw := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  rw [radialObjectiveAt_eq_scaledWall]
  have hg := scaled_moreau_gradient (f := radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * R))
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) < 9 / 2) (radialWall_lipschitz hl _)
    (radialWall_weaklyConvex (by norm_num) hw _) x
  norm_num at hg
  exact hg

theorem radial_exterior_gradient {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E) (hx : 4 * radialRadius M N ≤ ‖x‖) :
    ‖gradient (moreauEnvelope (1 / 2) (radialObjective U)) x‖ = 1 := by
  have hNpos : 0 < N := by omega
  have hl := isometricLift_lipschitz U (by norm_num : (0 : ℝ) ≤ 2) (chainMajorant_lipschitz hNpos)
  have hw := isometricLift_weaklyConvex U (by norm_num : (0 : ℝ) ≤ 9 / 2) (chainMajorant_weaklyConvex hNpos)
  have hout : 4 * ((2 / 3 : ℝ) * radialRadius M N) ≤ ‖(2 / 3 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hg := radialWall_moreau_exterior hl hw (scaled_radius_ge_one hM) hout
  rw [radialObjective, radialObjectiveAt_moreau_gradient hN, norm_smul, Real.norm_eq_abs]
  rw [hg]
  norm_num

variable [FiniteDimensional ℝ E]

theorem radial_moreau_barrier {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (U : ChainSpace M N →ₗᵢ[ℝ] E) (x : E)
    (s : Finset (Fin M × Fin N)) (hcard : N ≤ s.card)
    (hsmall : ∀ i ∈ s, isometryProjection U ((2 / 3 : ℝ) • x) i ≤ robustTolerance M N) :
    1 / (32 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 2) (radialObjective U)) x‖ := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcoverage : chainSourceRadius M N ≤ (8 : ℝ) ^ (3 * N) * chainNearRadius N := by
    simpa only [chainNearRadius, div_eq_mul_inv, one_mul] using chain_source_radius_threeN_coverage hN hMmax
  have hmargin : 96 * chainRadialConstant M N * (25 * (N : ℝ) + 8 * ((3 * N : ℕ) : ℝ)) ≤
      (2 / 3 : ℝ) * radialRadius M N - (5 * (M : ℝ) / N) / 3 := by
    convert radial_radius_margin hM hN using 1 <;> first | rfl | (push_cast; ring)
  have hb := chainRadialWall_moreau_barrier hN (scaled_radius_ge_one hM)
    (initial_gap_le_five hM hN) hcoverage hmargin U ((2 / 3 : ℝ) • x) s hcard
    (fun i hi => (hsmall i hi).trans (robustTolerance_le_inv_N M hNpos))
  have hn : ‖gradient (moreauEnvelope (1 / 2) (radialObjective U)) x‖ =
      (1 / 3 : ℝ) * ‖gradient (moreauEnvelope (1 / 9)
        (radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * radialRadius M N))) ((2 / 3 : ℝ) • x)‖ := by
    rw [radialObjective, radialObjectiveAt_moreau_gradient hN, norm_smul, Real.norm_eq_abs]
    norm_num
  have hscale : ‖gradient (moreauEnvelope (1 / 9)
        (radialWall (isometricLift U chainMajorant) ((2 / 3 : ℝ) * radialRadius M N))) ((2 / 3 : ℝ) • x)‖ =
      3 * ‖gradient (moreauEnvelope (1 / 2) (radialObjective U)) x‖ := by linarith
  rw [hscale] at hb
  apply strict_barrier_from_square hNR (by positivity : 0 < 49 * (N : ℝ)) (le_refl _) (norm_nonneg _)
  have hdiv := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 9)
  convert hdiv using 1 <;> first | rfl | (push_cast; ring)

end MP
