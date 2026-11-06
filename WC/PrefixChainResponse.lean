import WC.ChainWall
import WC.PrefixAnalysis
import WC.ParametricOracle

/-! Globally defined genuine complete-oracle responses on every orthonormal prefix. -/

noncomputable section
namespace WC
open scoped BigOperators Classical
set_option maxHeartbeats 600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev ChainPrefix (M N : ℕ) (s : Finset (Fin M × Fin N)) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {u : {i : Fin M × Fin N // i ∈ s} → E // Orthonormal ℝ u}

def prefixChainBase {M N : ℕ} (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) (x : E) : ℝ :=
  chainMajorant (prefixCoordinates s u.val x)

def prefixChainWall {M N : ℕ} (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) : E → ℝ :=
  scaleFunction (1 / 2) (2 / 3) (radialWall (prefixChainBase s u) (chainWallRadius M N))

theorem prefixChainBase_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) :
    Admissible 2 (9 / 2) (6 * (M : ℝ) / N) (prefixChainBase s u) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hbase : Admissible 2 (9 / 2) (6 * (M : ℝ) / N) (chainMajorant (M := M) (N := N)) :=
    ⟨chainMajorant_weaklyConvex hNpos, chainMajorant_lipschitz hNpos, chainMajorant_gapBound hM hN⟩
  exact hbase.precomp_contraction (by norm_num) (by norm_num) (prefixAnalysisLinear s u.val)
    (prefixCoordinates_norm_le s u.val u.property)

theorem prefixChainWall_admissible {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N)
    (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) :
    Admissible 1 1 (3 * (M : ℝ) / N) (prefixChainWall s u) := by
  have hbase := prefixChainBase_admissible hM hN s u
  have hwall : Admissible 3 (9 / 2) (6 * (M : ℝ) / N)
      (radialWall (prefixChainBase s u) (chainWallRadius M N)) :=
    ⟨radialWall_weaklyConvex (by norm_num) hbase.weaklyConvex _,
      radialWall_lipschitz hbase.lipschitz _,
      radialWall_gapBound hbase.gap ((by norm_num : (0 : ℝ) ≤ 1).trans (chainWallRadius_ge_one M N hN))⟩
  have h := admissible_scale (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 2 / 3) hwall
  norm_num at h
  convert h using 1 <;> first | rfl | ring

@[simp] theorem prefixChainBase_zero {M N : ℕ} (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) :
    prefixChainBase s u 0 = chainMajorant (0 : ChainSpace M N) := by
  have hzero := (prefixAnalysisLinear s u.val).map_zero
  change prefixCoordinates s u.val 0 = 0 at hzero
  exact congrArg chainMajorant hzero

theorem prefixChainWall_formula {M N : ℕ} (s : Finset (Fin M × Fin N)) (u : ChainPrefix M N s E) (x : E) :
    prefixChainWall s u x = (1 / 2 : ℝ) *
      max (chainMajorant (prefixCoordinates s u.val ((2 / 3 : ℝ) • x)))
        (chainMajorant (0 : ChainSpace M N) + 3 * (‖(2 / 3 : ℝ) • x‖ - chainWallRadius M N)) := by
  unfold prefixChainWall scaleFunction radialWall radialBranch
  rw [prefixChainBase_zero]
  rfl

theorem prefixChainBase_joint_continuous {M N : ℕ} (hN : 0 < N) (s : Finset (Fin M × Fin N)) :
    Continuous (fun p : ChainPrefix M N s E × E => prefixChainBase s p.1 p.2) := by
  have hu : Continuous (fun p : ChainPrefix M N s E × E => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hcoords := (prefixCoordinates_continuous s).comp (hu.prodMk continuous_snd)
  exact (chainMajorant_continuous hN).comp hcoords

theorem prefixChainWall_joint_continuous {M N : ℕ} (hN : 0 < N) (s : Finset (Fin M × Fin N)) :
    Continuous (fun p : ChainPrefix M N s E × E => prefixChainWall s p.1 p.2) := by
  have hscaled : Continuous (fun p : ChainPrefix M N s E × E => (2 / 3 : ℝ) • p.2) :=
    continuous_const.smul continuous_snd
  have hbase := (prefixChainBase_joint_continuous hN s).comp (continuous_fst.prodMk hscaled)
  have hbranch : Continuous (fun p : ChainPrefix M N s E × E =>
      chainMajorant (0 : ChainSpace M N) + 3 * (‖(2 / 3 : ℝ) • p.2‖ - chainWallRadius M N)) :=
    continuous_const.add (continuous_const.mul (hscaled.norm.sub continuous_const))
  have h : Continuous (fun p : ChainPrefix M N s E × E => (1 / 2 : ℝ) *
      max (prefixChainBase s p.1 ((2 / 3 : ℝ) • p.2))
        (chainMajorant (0 : ChainSpace M N) + 3 * (‖(2 / 3 : ℝ) • p.2‖ - chainWallRadius M N))) :=
    continuous_const.mul (hbase.max hbranch)
  convert h using 1
  funext p
  exact prefixChainWall_formula s p.1 p.2

instance chainPrefix_measurableSpace (M N : ℕ) (s : Finset (Fin M × Fin N)) :
    MeasurableSpace (ChainPrefix M N s E) := borel _
instance chainPrefix_borelSpace (M N : ℕ) (s : Finset (Fin M × Fin N)) :
    BorelSpace (ChainPrefix M N s E) := ⟨rfl⟩

variable [ProperSpace E] [CompleteSpace E]

def prefixChainResponse {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) (s : Finset (Fin M × Fin N))
    (p : E × ChainPrefix M N s E) : ℝ × CompactConvexSets E :=
  fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (prefixChainWall_admissible hM hN s p.2).lipschitz
    (prefixChainWall_admissible hM hN s p.2).weaklyConvex p.1

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem prefixChainResponse_measurable {M N : ℕ} (hM : 0 < M) (hN : 256 ≤ N) (s : Finset (Fin M × Fin N)) :
    Measurable (prefixChainResponse (E := E) hM hN s) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have h := parameterized_fullOracle_measurable (α := ChainPrefix M N s E) (E := E)
    (f := prefixChainWall s) (G := 1) (ρ := 1)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (prefixChainWall_joint_continuous (E := E) hNpos s)
    (fun u => (prefixChainWall_admissible hM hN s u).lipschitz)
    (fun u => (prefixChainWall_admissible hM hN s u).weaklyConvex)
  have hswap : Measurable (fun p : E × ChainPrefix M N s E => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  convert h.comp hswap using 1
  funext p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply TopologicalSpace.NonemptyCompacts.ext
    rfl

end WC
