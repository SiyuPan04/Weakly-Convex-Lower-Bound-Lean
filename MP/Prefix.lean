import MP.Radial
import WC.PrefixChainResponse

/-! The exact MP radial objective on every orthonormal prefix, with
uniform regularity and a genuine Borel full-oracle response everywhere. -/

noncomputable section
namespace MP
open WC
set_option maxHeartbeats 600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def prefixObjectiveAt {M N : ℕ} (R : ℝ) (s : Finset (Fin M × Fin N))
    (u : ChainPrefix M N s E) (x : E) : ℝ :=
  max ((1 / 2 : ℝ) * prefixChainBase s u ((2 / 3 : ℝ) • x))
    ((1 / 2 : ℝ) * chainMajorant (0 : ChainSpace M N) + ‖x‖ - R)

def prefixObjective {M N : ℕ} (s : Finset (Fin M × Fin N))
    (u : ChainPrefix M N s E) : E → ℝ := prefixObjectiveAt (radialRadius M N) s u

theorem prefixObjectiveAt_scaledWall {M N : ℕ} (R : ℝ) (s : Finset (Fin M × Fin N))
    (u : ChainPrefix M N s E) :
    prefixObjectiveAt R s u = scaleFunction (1 / 2) (2 / 3)
      (radialWall (prefixChainBase s u) ((2 / 3 : ℝ) * R)) := by
  funext x
  simp only [prefixObjectiveAt, scaleFunction, radialWall, radialBranch, prefixChainBase_zero,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

theorem prefixObjectiveAt_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    {R : ℝ} (hR : 0 ≤ R) (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (prefixObjectiveAt R s u) := by
  have hbase := prefixChainBase_admissible hM hN s u
  have hwall : Admissible 3 (9 / 2) (6 * (M : ℝ) / N)
      (radialWall (prefixChainBase s u) ((2 / 3 : ℝ) * R)) :=
    ⟨radialWall_weaklyConvex (by norm_num) hbase.weaklyConvex _,
      radialWall_lipschitz hbase.lipschitz _, radialWall_gapBound hbase.gap (by positivity)⟩
  have h := admissible_scale (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hwall
  norm_num at h
  rw [prefixObjectiveAt_scaledWall]
  convert h using 1
  first | rfl | ring

theorem prefix_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (prefixObjective s u) :=
  prefixObjectiveAt_admissible hM hN (radialRadius_pos hM).le s u

theorem prefixObjectiveAt_joint_continuous {M N : ℕ} (hN : 0 < N)
    (R : ℝ) (s : Finset (Fin M × Fin N)) :
    Continuous (fun p : ChainPrefix M N s E × E => prefixObjectiveAt R s p.1 p.2) := by
  have hscaled : Continuous (fun p : ChainPrefix M N s E × E => (2 / 3 : ℝ) • p.2) :=
    continuous_const.smul continuous_snd
  exact (continuous_const.mul ((prefixChainBase_joint_continuous hN s).comp
    (continuous_fst.prodMk hscaled))).max ((continuous_const.add continuous_snd.norm).sub continuous_const)

variable [ProperSpace E] [CompleteSpace E]

def prefixResponse {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) (s : Finset (Fin M × Fin N))
    (p : E × ChainPrefix M N s E) : ℝ × CompactConvexSets E :=
  fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (prefix_admissible hM hN s p.2).lipschitz (prefix_admissible hM hN s p.2).weaklyConvex p.1

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem prefixResponse_measurable {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (s : Finset (Fin M × Fin N)) : Measurable (prefixResponse (E := E) hM hN s) := by
  have h := parameterized_fullOracle_measurable (α := ChainPrefix M N s E) (E := E)
    (f := prefixObjective s) (G := 1) (ρ := 1) (by norm_num) (by norm_num)
    (prefixObjectiveAt_joint_continuous (by omega : 0 < N) (radialRadius M N) s)
    (fun u => (prefix_admissible hM hN s u).lipschitz)
    (fun u => (prefix_admissible hM hN s u).weaklyConvex)
  have hswap : Measurable (fun p : E × ChainPrefix M N s E => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  convert h.comp hswap using 1
  funext p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply TopologicalSpace.NonemptyCompacts.ext
    rfl

end MP
