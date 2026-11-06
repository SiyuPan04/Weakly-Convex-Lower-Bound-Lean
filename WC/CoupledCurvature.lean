import WC.CoupledRegularity
import WC.BlockSubgradient
import Mathlib.Analysis.Convex.Continuous

/-! Uniform weak convexity of sums on disjoint blocks and the actual coupled maximum. -/

noncomputable section
namespace WC

open scoped BigOperators

theorem sum_euclideanBlock_norm_sq {M N : ℕ} (x : ChainSpace M N) :
    (∑ m, ‖euclideanBlock x m‖ ^ 2) = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, euclideanBlock]
  exact (Fintype.sum_prod_type (fun i : Fin M × Fin N => x i ^ 2)).symm

theorem weaklyConvex_blockSum {M N : ℕ} {L : ℝ}
    (f : Fin M → EuclideanSpace ℝ (Fin N) → ℝ) (hf : ∀ m, WeaklyConvex L (f m)) :
    WeaklyConvex L (fun x : ChainSpace M N => ∑ m, f m (euclideanBlock x m)) := by
  have hid (z : ChainSpace M N) :
      (∑ m, f m (euclideanBlock z m)) + L / 2 * ‖z‖ ^ 2 =
        ∑ m, (f m (euclideanBlock z m) + L / 2 * ‖euclideanBlock z m‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_euclideanBlock_norm_sq]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change (∑ m, f m (euclideanBlock (a • x + b • y) m)) + L / 2 * ‖a • x + b • y‖ ^ 2 ≤
    a * ((∑ m, f m (euclideanBlock x m)) + L / 2 * ‖x‖ ^ 2) +
    b * ((∑ m, f m (euclideanBlock y m)) + L / 2 * ‖y‖ ^ 2)
  rw [hid, hid x, hid y, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  have h := (hf m).2 (Set.mem_univ (euclideanBlock x m))
    (Set.mem_univ (euclideanBlock y m)) ha hb hab
  convert h using 1 <;> rfl

theorem weaklyConvex_add_convex_fn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} {f g : E → ℝ} (hf : WeaklyConvex L f) (hg : ConvexOn ℝ Set.univ g) :
    WeaklyConvex L (fun x => f x + g x) := by
  have h := hf.add hg
  unfold WeaklyConvex
  convert h using 1 <;> first | rfl | (funext x; dsimp; ring)

theorem weaklyConvex_const_mul_fn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L a : ℝ} {f : E → ℝ} (ha : 0 ≤ a) (hf : WeaklyConvex L f) :
    WeaklyConvex (a * L) (fun x => a * f x) := by
  have h := ConvexOn.smul ha hf
  unfold WeaklyConvex
  convert h using 1 <;> first | rfl | (funext x; dsimp; ring)

theorem weaklyConvex_add_const_fn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} {f : E → ℝ} (hf : WeaklyConvex L f) (c : ℝ) :
    WeaklyConvex L (fun x => f x + c) :=
  weaklyConvex_add_convex_fn hf (convexOn_const c convex_univ)

theorem weaklyConvex_weightedCoupledFunction {M N : ℕ} (hN : 0 < N)
    (w : EuclideanSpace ℝ (Fin M)) (hw : w ∈ scoreWeights) :
    WeaklyConvex (9 / 2 : ℝ) (weightedCoupledFunction w (N := N)) := by
  let f (m : Fin M) (u : EuclideanSpace ℝ (Fin N)) : ℝ :=
    smoothBlockTerm (nextWeight w m) u +
      w m * (euclideanTiltedBlock N (M * N) m.val u - 5 / 4)
  have hf (m : Fin M) : WeaklyConvex (9 * (N : ℝ) / 4) (f m) := by
    apply weaklyConvex_add_convex_fn
      (weaklyConvex_smoothBlockTerm hN (nextWeight_nonneg hw m) (nextWeight_le_one hw m))
    have h := ConvexOn.smul (hw.1 m)
      ((convexOn_euclideanTiltedBlock N (M * N) m.val).add_const (-(5 / 4 : ℝ)))
    convert h using 1 <;> rfl
  have hs := weaklyConvex_blockSum f hf
  have hc := weaklyConvex_add_const_fn hs (initialWeight w)
  have hscaled := weaklyConvex_const_mul_fn (show 0 ≤ 2 / (N : ℝ) by positivity) hc
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : (2 / (N : ℝ)) * (9 * (N : ℝ) / 4) = 9 / 2 := by field_simp; norm_num
  rw [hL] at hscaled
  have heq : weightedCoupledFunction w (N := N) =
      (fun x : ChainSpace M N => (2 / (N : ℝ)) *
        ((∑ m, f m (euclideanBlock x m)) + initialWeight w)) := by
    funext x
    rw [weightedCoupledFunction_grouped]
    simp only [f, euclideanTiltedBlock, euclideanBlock, Finset.sum_add_distrib]
    ring
  rw [heq]
  exact hscaled

/-- Lemma `lem:coupled-curvature`: the explicit coupled function is `9/2`-weakly convex. -/
theorem weaklyConvex_coupledFunction {M N : ℕ} (hN : 0 < N) :
    WeaklyConvex (9 / 2 : ℝ) (coupledFunction (M := M) (N := N)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let w := positiveScoreOptimizer (coupledScores z)
  have hw : w ∈ scoreWeights := positiveScoreOptimizer_mem _
  have hc := (weaklyConvex_weightedCoupledFunction hN w hw).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  change weightedCoupledFunction w z + (9 / 2 : ℝ) / 2 * ‖z‖ ^ 2 ≤
    a * (weightedCoupledFunction w x + (9 / 2 : ℝ) / 2 * ‖x‖ ^ 2) +
    b * (weightedCoupledFunction w y + (9 / 2 : ℝ) / 2 * ‖y‖ ^ 2) at hc
  have hopt : weightedCoupledFunction w z = coupledFunction z := weightedCoupledFunction_attains z
  rw [hopt] at hc
  exact hc.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (weightedCoupledFunction_le w x hw) le_rfl) ha)
    (mul_le_mul_of_nonneg_left (add_le_add (weightedCoupledFunction_le w y hw) le_rfl) hb))

theorem weaklyConvex_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : ℝ} {f : E → ℝ} (hf : WeaklyConvex L f) : Continuous f := by
  have hc : Continuous (fun x => f x + L / 2 * ‖x‖ ^ 2) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hf)
  have hq : Continuous (fun x : E => L / 2 * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  have h := hc.sub hq
  convert h using 1
  funext x
  dsimp
  ring

theorem continuous_coupledFunction {M N : ℕ} (hN : 0 < N) :
    Continuous (coupledFunction (M := M) (N := N)) :=
  weaklyConvex_continuous (weaklyConvex_coupledFunction hN)

end WC
