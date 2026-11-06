import WC.Progress
import WC.Smooth

/-! Quantitative smoothness of the relay block term `G_ω` from the manuscript. -/

noncomputable section
namespace WC

def relayProgress (s : ℝ) : ℝ := progressGate ((4 * s - 1) / 3)
def relaySlope (s : ℝ) : ℝ := (4 / 3) * progressGateSlope ((4 * s - 1) / 3)

theorem hasDerivAt_relayProgress (s : ℝ) : HasDerivAt relayProgress (relaySlope s) s := by
  have ha : HasDerivAt (fun t : ℝ => (4 * t - 1) / 3) (4 / 3) s := by
    convert (((hasDerivAt_id s).const_mul 4).sub_const 1).div_const 3 using 1 <;>
      first | rfl | norm_num
  have h := (hasDerivAt_progressGate ((4 * s - 1) / 3)).comp s ha
  change HasDerivAt (fun t => progressGate ((4 * t - 1) / 3))
    ((4 / 3) * progressGateSlope ((4 * s - 1) / 3)) s
  convert h using 1 <;> first | rfl | ring

theorem relaySlope_nonneg (s : ℝ) : 0 ≤ relaySlope s := by
  exact mul_nonneg (by norm_num) (progressGateSlope_nonneg _)

theorem relaySlope_le (s : ℝ) : relaySlope s ≤ 2 := by
  unfold relaySlope
  have h := progressGateSlope_le ((4 * s - 1) / 3)
  linarith

theorem relaySlope_abs_sub_le (s t : ℝ) :
    |relaySlope s - relaySlope t| ≤ (32 / 3) * |s - t| := by
  have ha : |(4 * s - 1) / 3 - (4 * t - 1) / 3| = (4 / 3) * |s - t| := by
    have heq : (4 * s - 1) / 3 - (4 * t - 1) / 3 = (4 / 3) * (s - t) := by ring
    rw [heq, abs_mul]
    norm_num
  unfold relaySlope
  calc
    _ = (4 / 3) * |progressGateSlope ((4 * s - 1) / 3) -
        progressGateSlope ((4 * t - 1) / 3)| := by rw [← mul_sub, abs_mul]; norm_num
    _ ≤ (4 / 3) * (6 * |(4 * s - 1) / 3 - (4 * t - 1) / 3|) :=
      mul_le_mul_of_nonneg_left (progressGateSlope_abs_sub_le _ _) (by norm_num)
    _ = _ := by rw [ha]; ring

theorem relayProgress_abs_sub_le (s t : ℝ) : |relayProgress s - relayProgress t| ≤ 2 * |s - t| := by
  have ha : |(4 * s - 1) / 3 - (4 * t - 1) / 3| = (4 / 3) * |s - t| := by
    have heq : (4 * s - 1) / 3 - (4 * t - 1) / 3 = (4 / 3) * (s - t) := by ring
    rw [heq, abs_mul]
    norm_num
  have h := lipschitzWith_progressGate.dist_le_mul ((4 * s - 1) / 3) ((4 * t - 1) / 3)
  change |relayProgress s - relayProgress t| ≤ (3 / 2) *
    |(4 * s - 1) / 3 - (4 * t - 1) / 3| at h
  rw [ha] at h
  calc
    _ ≤ (3 / 2) * ((4 / 3) * |s - t|) := h
    _ = _ := by ring

theorem antitone_weightedRelay {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    Antitone (fun s : ℝ => ω * relayProgress s - 2 * s) := by
  intro s t hst
  have hdiff : relayProgress t - relayProgress s ≤ 2 * (t - s) := by
    have h := relayProgress_abs_sub_le t s
    rw [abs_of_nonneg (sub_nonneg.mpr hst)] at h
    exact le_trans (le_abs_self _) h
  have hw := mul_le_mul_of_nonneg_left hdiff hω0
  have hw1 := mul_le_mul_of_nonneg_right hω1 (show 0 ≤ 2 * (t - s) by positivity)
  nlinarith

def smoothBlockTerm {N : ℕ} (ω : ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ω * relayProgress (euclideanProgress x) - 2 * euclideanProgress x

def smoothBlockGradient {N : ℕ} (ω : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) :=
  (ω * relaySlope (euclideanProgress x) - 2) • progressGradient x

theorem antitone_smoothBlockTerm {N : ℕ} {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (x y : EuclideanSpace ℝ (Fin N)) (hxy : ∀ n, x n ≤ y n) :
    smoothBlockTerm ω y ≤ smoothBlockTerm ω x := by
  apply antitone_weightedRelay hω0 hω1
  exact monotone_blockProgress hxy

theorem hasFDerivAt_smoothBlockTerm {N : ℕ} (hN : 0 < N) (ω : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    HasFDerivAt (smoothBlockTerm ω) (innerSL ℝ (smoothBlockGradient ω x)) x := by
  have hp := (hasGradientAt_euclideanProgress hN x).hasFDerivAt
  have hr := (hasDerivAt_relayProgress (euclideanProgress x)).comp_hasFDerivAt x hp
  have h := (hr.const_mul ω).sub (hp.const_mul 2)
  convert h using 1
  all_goals try rfl
  ext y
  simp [smoothBlockGradient, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  ring

theorem smoothBlockCoefficient_abs_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (s : ℝ) :
    |ω * relaySlope s - 2| ≤ 2 := by
  have h0 := relaySlope_nonneg s
  have h1 := relaySlope_le s
  have hp := mul_nonneg hω0 h0
  have hu := mul_le_mul_of_nonneg_right hω1 h0
  apply abs_le.mpr
  constructor <;> linarith

theorem smoothBlockGradient_norm_sub_le {N : ℕ} (hN : 0 < N) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (x y : EuclideanSpace ℝ (Fin N)) :
    ‖smoothBlockGradient ω x - smoothBlockGradient ω y‖ ≤
      (9 * (N : ℝ) / 4) * ‖x - y‖ := by
  let A : ℝ := 3 * Real.sqrt (N : ℝ) / 8
  let ax := ω * relaySlope (euclideanProgress x) - 2
  let ay := ω * relaySlope (euclideanProgress y) - 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hax : |ax| ≤ 2 := smoothBlockCoefficient_abs_le hω0 hω1 _
  have hadiff : |ax - ay| ≤ ((32 / 3) * A) * ‖x - y‖ := by
    have heq : ax - ay = ω * (relaySlope (euclideanProgress x) -
        relaySlope (euclideanProgress y)) := by dsimp [ax, ay]; ring
    rw [heq, abs_mul, abs_of_nonneg hω0]
    calc
      _ ≤ 1 * |relaySlope (euclideanProgress x) - relaySlope (euclideanProgress y)| :=
        mul_le_mul_of_nonneg_right hω1 (abs_nonneg _)
      _ ≤ (32 / 3) * |euclideanProgress x - euclideanProgress y| := by
        simpa only [one_mul] using relaySlope_abs_sub_le (euclideanProgress x) (euclideanProgress y)
      _ ≤ (32 / 3) * (A * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (euclideanProgress_abs_sub_le hN x y) (by norm_num)
      _ = _ := by ring
  have hnormy : ‖progressGradient y‖ ≤ A := progressGradient_norm_le y
  have hglip := progressGradient_norm_sub_le x y
  have heq : smoothBlockGradient ω x - smoothBlockGradient ω y =
      ax • (progressGradient x - progressGradient y) + (ax - ay) • progressGradient y := by
    dsimp [smoothBlockGradient, ax, ay]
    module
  have hconst : 2 * (3 * (N : ℝ) / 8) + (32 / 3) * A ^ 2 = 9 * (N : ℝ) / 4 := by
    dsimp [A]
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith
  calc
    _ ≤ |ax| * ‖progressGradient x - progressGradient y‖ + |ax - ay| * ‖progressGradient y‖ := by
      rw [heq]
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (ax • (progressGradient x - progressGradient y)) ((ax - ay) • progressGradient y)
    _ ≤ 2 * ((3 * (N : ℝ) / 8) * ‖x - y‖) + (((32 / 3) * A) * ‖x - y‖) * A := by
      apply add_le_add
      · exact mul_le_mul hax hglip (norm_nonneg _) (by norm_num)
      · exact mul_le_mul hadiff hnormy (norm_nonneg _) (by positivity)
    _ = (2 * (3 * (N : ℝ) / 8) + (32 / 3) * A ^ 2) * ‖x - y‖ := by ring
    _ = _ := by rw [hconst]

theorem weaklyConvex_smoothBlockTerm {N : ℕ} (hN : 0 < N) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    WeaklyConvex (9 * (N : ℝ) / 4) (smoothBlockTerm (N := N) ω) :=
  weaklyConvex_of_lipschitz_derivative (by positivity)
    (hasFDerivAt_smoothBlockTerm hN ω) (smoothBlockGradient_norm_sub_le hN hω0 hω1)

end WC
