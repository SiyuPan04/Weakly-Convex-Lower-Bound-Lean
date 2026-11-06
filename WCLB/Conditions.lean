import WC.MaskedSubdifferential
import WC.DiagonalSubspaces
import WC.InitialGap
import WC.ChainWall
import WC.CoreFiltration

/-! Exact four unscaled conditions of the WCLB manuscript.
Index `r : ℕ` represents manuscript time `t=r−1`, so `I 0=∅`
is its `I₋₁` and the next prefix is `I (r+1)`. -/

noncomputable section
namespace WCLB
open scoped Classical

def coordinateProjection {M N : ℕ} (s : Finset (Fin M × Fin N))
    (x : WC.ChainSpace M N) : WC.ChainSpace M N :=
  WithLp.toLp 2 (fun i => if i ∈ s then x i else 0)

@[simp] theorem coordinateProjection_exposed {M N : ℕ} (r : ℕ) (x : WC.ChainSpace M N) :
    coordinateProjection (WC.exposedIndices M N r) x = WC.diagonalMask M N r x := by
  ext i
  simp only [coordinateProjection, WC.diagonalMask_apply, WC.exposedIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- A faithful proposition-valued record of Condition `cond:hard-instance`.
Its concrete construction must prove every field; defining this structure
does not assert existence of such a construction. -/
structure UnscaledHardInstanceConditions (M N T : ℕ) (f : WC.ChainSpace M N → ℝ)
    (I : ℕ → Finset (Fin M × Fin N)) : Prop where
  filtration_initial : I 0 = ∅
  filtration_mono : Monotone I
  horizon_positive : 0 < T
  weaklyConvex : WC.WeaklyConvex (9 / 2 : ℝ) f
  lipschitz : WC.GloballyLipschitz 2 f
  bounded_below : BddBelow (Set.range f)
  locality : ∀ r x, (∀ i, i ∉ I r → |x i| < WC.robustTolerance M N) →
    f x = f (coordinateProjection (I (r + 1)) x) ∧
      WC.subdifferential f x = WC.subdifferential f (coordinateProjection (I (r + 1)) x) ∧
      WC.subdifferential f x ⊆ (WC.coordinateSpan (I (r + 1)) : Set (WC.ChainSpace M N))
  horizon_bound : (M * N : ℕ) ≤ 16 * T
  terminal_barrier : ∀ x, (∀ i, i ∉ I T → |x i| < WC.robustTolerance M N) →
    1 / (10 * Real.sqrt (N : ℝ)) < ‖gradient (WC.moreauEnvelope (1 / 9) f) x‖
  gap : WC.GapBound (5 * (M : ℝ) / N) f

theorem coordinateSpan_mem_of_zero_off {M N : ℕ} (s : Finset (Fin M × Fin N))
    (v : WC.ChainSpace M N) (hv : ∀ i, i ∉ s → v i = 0) :
    v ∈ WC.coordinateSpan s := by
  let b := EuclideanSpace.basisFun (Fin M × Fin N) ℝ
  rw [← b.sum_repr v]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ s
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  · have hzero : b.repr v i = 0 := by simpa only [b, EuclideanSpace.basisFun_repr] using hv i hi
    rw [hzero, zero_smul]
    exact Submodule.zero_mem _

theorem chainMajorant_gap_five {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N) :
    WC.GapBound (5 * (M : ℝ) / N) (WC.chainMajorant (M := M) (N := N)) := by
  apply WC.gapBound_iff_inf.mpr
  refine ⟨(WC.chainMajorant_gapBound (by omega) hN).bddBelow, ?_⟩
  rw [WC.chainMajorant_gap (by omega : 0 < M) hN]
  have hγ := (WC.initialGamma_bounds (by omega : 0 < M) (by omega : 0 < N)).2
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnum : 2 * (2 * (M : ℝ) + WC.initialGamma M N) ≤ 5 * (M : ℝ) := by linarith
  have hden : (0 : ℝ) ≤ N := by positivity
  have h := div_le_div_of_nonneg_right hnum hden
  convert h using 1 <;> first | rfl | ring

/-- Construction of all four conditions from the separate actual raw
Moreau-barrier theorem. The supplied premise is precisely that theorem,
and the final concrete certificate instantiates it with a proof. -/
theorem chainMajorant_conditions_of_terminal {M N : ℕ} (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hterminal : ∀ x : WC.ChainSpace M N,
      (∀ i, i ∉ WC.exposedIndices M N ((M - 1) * WC.stagger N) →
        |x i| < WC.robustTolerance M N) →
      1 / (10 * Real.sqrt (N : ℝ)) < ‖gradient (WC.moreauEnvelope (1 / 9) WC.chainMajorant) x‖) :
    UnscaledHardInstanceConditions M N ((M - 1) * WC.stagger N)
      WC.chainMajorant (WC.exposedIndices M N) := by
  refine ⟨WC.exposedIndices_zero M N, fun _ _ h => WC.exposedIndices_mono M N h,
    WC.diagonal_horizon_positive hM hN, WC.chainMajorant_weaklyConvex (by omega),
    WC.chainMajorant_lipschitz (by omega), (chainMajorant_gap_five hM hN).bddBelow,
    ?_, WC.horizon_bound hM hN, hterminal, chainMajorant_gap_five hM hN⟩
  intro r x hidden
  have htube : x ∈ WC.diagonalTube M N r := by
    intro i hi
    apply hidden
    simp only [WC.exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [coordinateProjection_exposed]
    exact WC.chainMajorant_diagonalMask_eq (by omega) hN x r (fun i hi => (htube i hi).le)
  · rw [coordinateProjection_exposed]
    exact WC.chainMajorant_diagonalMask_subdifferential_eq (by omega) hN x r htube
  · intro v hv
    apply coordinateSpan_mem_of_zero_off
    intro i hi
    apply WC.chainMajorant_subgradient_diagonal_zero (by omega) hN x r
      (fun j hj => (htube j hj).le) hv i
    simp only [WC.exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    omega

end WCLB
