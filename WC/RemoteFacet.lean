import WC.RawBarrier
import WC.ChainSources

/-! A positively weighted fan at a remote majorant source has one unique active facet. -/

noncomputable section
namespace WC
open scoped BigOperators Classical
open Filter Topology

theorem coupledFacetBranchGradient_mem_subdifferential {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) (hactive : coupledFacetBranch w a x = coupledFunction x) :
    coupledFacetBranchGradient w a x ∈ subdifferential coupledFunction x := by
  rw [subdifferential_coupledFunction_eq_convexHull hN]
  apply subset_convexHull
  exact ⟨w, hw, a, hactive, rfl⟩

theorem affineFacetGradient_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (affineFacetGradient N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some n =>
      have h := congrArg (fun g : EuclideanSpace ℝ (Fin N) => g n) hab
      simp [affineFacetGradient] at h
      linarith
  | some n =>
    cases b with
    | none =>
      have h := congrArg (fun g : EuclideanSpace ℝ (Fin N) => g n) hab
      simp [affineFacetGradient] at h
      linarith
    | some p =>
      by_cases hnp : n = p
      · exact congrArg some hnp
      · have h := congrArg (fun g : EuclideanSpace ℝ (Fin N) => g n) hab
        simp [affineFacetGradient, hnp] at h
        linarith

theorem coupledFacetBranch_update_eq {M N : ℕ} (w : EuclideanSpace ℝ (Fin M))
    (a : Fin M → FanFacet N) (x : ChainSpace M N) (m : Fin M) (b : FanFacet N)
    (heq : affineFacet N (M * N) m.val b (euclideanBlock x m) =
      affineFacet N (M * N) m.val (a m) (euclideanBlock x m)) :
    coupledFacetBranch w (Function.update a m b) x = coupledFacetBranch w a x := by
  unfold coupledFacetBranch
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = m
  · subst j
    rw [Function.update_self, heq]
  · rw [Function.update_of_ne hj]

theorem remote_source_active_facet_unique {M N : ℕ} (hN : 0 < N)
    {z y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 z) (hzy : z ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (hactive : coupledFacetBranch w a y = coupledFunction y) (m : Fin M) (hwm : 0 < w m)
    (b : FanFacet N) (hb : affineFacet N (M * N) m.val b (euclideanBlock y m) =
      euclideanTiltedBlock N (M * N) m.val (euclideanBlock y m)) : b = a m := by
  have hgap := activeFacet_weighted_gap_zero hN w hw a y hactive m
  have horig : affineFacet N (M * N) m.val (a m) (euclideanBlock y m) =
      euclideanTiltedBlock N (M * N) m.val (euclideanBlock y m) := by
    have h := (mul_eq_zero.mp hgap).resolve_left hwm.ne'
    linarith
  have hupdated : coupledFacetBranch w (Function.update a m b) y = coupledFunction y :=
    (coupledFacetBranch_update_eq w a y m b (hb.trans horig.symm)).trans hactive
  have hgorig := coupledFacetBranchGradient_mem_subdifferential hN w hw a y hactive
  have hgupdate := coupledFacetBranchGradient_mem_subdifferential hN w hw (Function.update a m b) y hupdated
  have heqg : coupledFacetBranchGradient w (Function.update a m b) y = coupledFacetBranchGradient w a y :=
    (chain_remote_source_subgradient hN hy hzy hgupdate).trans
      (chain_remote_source_subgradient hN hy hzy hgorig).symm
  apply affineFacetGradient_injective hN
  apply PiLp.ext
  intro n
  have h := congrArg (fun v : ChainSpace M N => v (m, n)) heqg
  rw [coupledFacetBranchGradient_apply, coupledFacetBranchGradient_apply] at h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := mul_left_cancel₀ (ne_of_gt (by positivity : 0 < 2 / (N : ℝ))) h
  simp only [blockFacetGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Function.update_self] at hc
  have hmul : w m * affineFacetGradient N b n = w m * affineFacetGradient N (a m) n := by linarith
  exact mul_left_cancel₀ hwm.ne' hmul

theorem activeFacet_eq_tiltedBlock_of_weight_pos {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (x : ChainSpace M N) (hactive : coupledFacetBranch w a x = coupledFunction x)
    (m : Fin M) (hwm : 0 < w m) :
    affineFacet N (M * N) m.val (a m) (euclideanBlock x m) =
      euclideanTiltedBlock N (M * N) m.val (euclideanBlock x m) := by
  have h := (mul_eq_zero.mp (activeFacet_weighted_gap_zero hN w hw a x hactive m)).resolve_left hwm.ne'
  linarith

/-- A unique finite fan facet remains the unique maximizing facet on a neighborhood. -/
theorem affineFacet_unique_eventually (N K m : ℕ) (a : FanFacet N) (x : EuclideanSpace ℝ (Fin N))
    (ha : affineFacet N K m a x = euclideanTiltedBlock N K m x)
    (hunique : ∀ b, affineFacet N K m b x = euclideanTiltedBlock N K m x → b = a) :
    ∀ᶠ u in 𝓝 x, affineFacet N K m a u = euclideanTiltedBlock N K m u ∧
      ∀ b, affineFacet N K m b u = euclideanTiltedBlock N K m u → b = a := by
  have hev (b : FanFacet N) : ∀ᶠ u in 𝓝 x, b ≠ a → affineFacet N K m b u < affineFacet N K m a u := by
    by_cases hba : b = a
    · exact Filter.Eventually.of_forall fun _ h => (h hba).elim
    have hle := affineFacet_le_tiltedBlock N K m b x
    rw [← ha] at hle
    have hne : affineFacet N K m b x ≠ affineFacet N K m a x := fun h => hba (hunique b (h.trans ha))
    have hlt := lt_of_le_of_ne hle hne
    have ho : IsOpen {u | affineFacet N K m b u < affineFacet N K m a u} :=
      isOpen_lt (continuous_affineFacet N K m b) (continuous_affineFacet N K m a)
    filter_upwards [ho.mem_nhds hlt] with u hu _
    exact hu
  have hall := Filter.eventually_all.mpr hev
  filter_upwards [hall] with u hu
  have hle (b : FanFacet N) : affineFacet N K m b u ≤ affineFacet N K m a u := by
    by_cases hb : b = a
    · simp [hb]
    · exact (hu b hb).le
  have hblock : euclideanTiltedBlock N K m u ≤ affineFacet N K m a u :=
    tiltedBlock_le (hle none) (fun n => hle (some n))
  have hmax := le_antisymm (affineFacet_le_tiltedBlock N K m a u) hblock
  refine ⟨hmax, ?_⟩
  intro b hb
  by_contra hba
  have hlt := hu b hba
  rw [hb, ← hmax] at hlt
  exact lt_irrefl _ hlt

theorem remote_source_active_facet_eventually {M N : ℕ} (hN : 0 < N)
    {z y : ChainSpace M N} (hy : y ∈ majorantSources coupledFunction 2 z) (hzy : z ≠ y)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) (a : Fin M → FanFacet N)
    (hactive : coupledFacetBranch w a y = coupledFunction y) (m : Fin M) (hwm : 0 < w m) :
    ∀ᶠ u in 𝓝 (euclideanBlock y m), affineFacet N (M * N) m.val (a m) u =
      euclideanTiltedBlock N (M * N) m.val u ∧
      ∀ b, affineFacet N (M * N) m.val b u = euclideanTiltedBlock N (M * N) m.val u → b = a m :=
  affineFacet_unique_eventually N (M * N) m.val (a m) (euclideanBlock y m)
    (activeFacet_eq_tiltedBlock_of_weight_pos hN w hw a y hactive m hwm)
    (remote_source_active_facet_unique hN hy hzy w hw a hactive m hwm)

end WC
