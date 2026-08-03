import WeaklyConvexLowerBound.HardInstance

/-!
# Variational representation of the positive-part Euclidean aggregation

This file proves, without an external compact-max theorem, that
`sqrt (sum (max sᵢ 0)²)` is the support function of the nonnegative Euclidean
unit ball.  It supplies the exact maximizer used by the manuscript.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

def positiveNorm {M : Nat} (s : Fin M → ℝ) : ℝ :=
  Real.sqrt (∑ m, (max (s m) 0) ^ 2)

def outerDot {M : Nat} (w s : Fin M → ℝ) : ℝ :=
  ∑ m, w m * s m

def FeasibleOuterWeight {M : Nat} (w : Fin M → ℝ) : Prop :=
  (∀ m, 0 ≤ w m) ∧ (∑ m, (w m) ^ 2) ≤ 1

def canonicalOuterWeight {M : Nat} (s : Fin M → ℝ) : Fin M → ℝ :=
  fun m => max (s m) 0 / positiveNorm s

theorem positiveNorm_nonneg {M : Nat} (s : Fin M → ℝ) :
    0 ≤ positiveNorm s := Real.sqrt_nonneg _

theorem activationNorm_eq_positiveNorm {M N : Nat} (z : BlockVec M N) :
    activationNorm z = positiveNorm (sigmaScore z) := rfl

private theorem max_zero_mul_self (a : ℝ) :
    max a 0 * a = (max a 0) ^ 2 := by
  by_cases ha : a ≤ 0
  · simp [max_eq_right ha]
  · have ha0 : 0 ≤ a := le_of_not_ge ha
    simp [max_eq_left ha0, pow_two]

theorem outerDot_le_positiveNorm {M : Nat} {w s : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) :
    outerDot w s ≤ positiveNorm s := by
  have hterm (m : Fin M) : w m * s m ≤ w m * max (s m) 0 := by
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw.1 m)
  have hfirst : outerDot w s ≤ ∑ m, w m * max (s m) 0 := by
    unfold outerDot
    exact Finset.sum_le_sum fun m _ => hterm m
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin M)) w (fun m => max (s m) 0)
  have hwsum0 : 0 ≤ ∑ m, (w m) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hpsum0 : 0 ≤ ∑ m, (max (s m) 0) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hwsqrt0 := Real.sqrt_nonneg (∑ m, (w m) ^ 2)
  have hwsqrt_sq := Real.sq_sqrt hwsum0
  have hwsqrt_le : Real.sqrt (∑ m, (w m) ^ 2) ≤ 1 := by
    nlinarith [hw.2]
  have hpsqrt0 := Real.sqrt_nonneg (∑ m, (max (s m) 0) ^ 2)
  have hmul :
      Real.sqrt (∑ m, (w m) ^ 2) *
          Real.sqrt (∑ m, (max (s m) 0) ^ 2) ≤
        Real.sqrt (∑ m, (max (s m) 0) ^ 2) := by
    simpa using mul_le_mul_of_nonneg_right hwsqrt_le hpsqrt0
  exact hfirst.trans (hcs.trans (by simpa [positiveNorm] using hmul))

theorem canonicalOuterWeight_nonneg {M : Nat} (s : Fin M → ℝ)
    (m : Fin M) : 0 ≤ canonicalOuterWeight s m := by
  unfold canonicalOuterWeight
  exact div_nonneg (le_max_right _ _) (positiveNorm_nonneg s)

theorem canonicalOuterWeight_sq_sum {M : Nat} {s : Fin M → ℝ}
    (hpos : 0 < positiveNorm s) :
    (∑ m, (canonicalOuterWeight s m) ^ 2) = 1 := by
  have hsum0 : 0 ≤ ∑ m : Fin M, (max (s m) 0) ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hnormSq : positiveNorm s ^ 2 =
      ∑ m : Fin M, (max (s m) 0) ^ 2 := by
    unfold positiveNorm
    exact Real.sq_sqrt hsum0
  simp only [canonicalOuterWeight, div_pow]
  rw [← Finset.sum_div, ← hnormSq,
    div_self (pow_ne_zero 2 hpos.ne')]

theorem canonicalOuterWeight_feasible {M : Nat} (s : Fin M → ℝ) :
    FeasibleOuterWeight (canonicalOuterWeight s) := by
  constructor
  · exact canonicalOuterWeight_nonneg s
  · by_cases hpos : 0 < positiveNorm s
    · rw [canonicalOuterWeight_sq_sum hpos]
    · have hz : positiveNorm s = 0 :=
        le_antisymm (le_of_not_gt hpos) (positiveNorm_nonneg s)
      simp [canonicalOuterWeight, hz]

theorem canonicalOuterWeight_dot {M : Nat} (s : Fin M → ℝ) :
    outerDot (canonicalOuterWeight s) s = positiveNorm s := by
  by_cases hpos : 0 < positiveNorm s
  · have hsum0 : 0 ≤ ∑ m : Fin M, (max (s m) 0) ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have hnormSq : positiveNorm s ^ 2 =
        ∑ m : Fin M, (max (s m) 0) ^ 2 := by
      unfold positiveNorm
      exact Real.sq_sqrt hsum0
    unfold outerDot canonicalOuterWeight
    calc
      (∑ m, max (s m) 0 / positiveNorm s * s m) =
          (∑ m, (max (s m) 0) ^ 2) / positiveNorm s := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro m _
        calc
          max (s m) 0 / positiveNorm s * s m =
              (max (s m) 0 * s m) / positiveNorm s := by ring
          _ = (max (s m) 0) ^ 2 / positiveNorm s := by
            rw [max_zero_mul_self]
      _ = positiveNorm s ^ 2 / positiveNorm s := by rw [← hnormSq]
      _ = positiveNorm s := by field_simp [hpos.ne']
  · have hz : positiveNorm s = 0 :=
      le_antisymm (le_of_not_gt hpos) (positiveNorm_nonneg s)
    simp [outerDot, canonicalOuterWeight, hz]

/-- Exact support-function variational representation, including attainment. -/
theorem positiveNorm_variational {M : Nat} (s : Fin M → ℝ) :
    (∀ w, FeasibleOuterWeight w → outerDot w s ≤ positiveNorm s) ∧
      FeasibleOuterWeight (canonicalOuterWeight s) ∧
      outerDot (canonicalOuterWeight s) s = positiveNorm s := by
  exact ⟨fun _ => outerDot_le_positiveNorm,
    canonicalOuterWeight_feasible s, canonicalOuterWeight_dot s⟩

def activationBranch {M N : Nat} (w : Fin M → ℝ)
    (z : BlockVec M N) : ℝ :=
  (2 / (N : ℝ)) * (outerDot w (sigmaScore z) - ∑ m, psi (z m))

theorem activationBranch_le_hardValue {M N : Nat} (hN : 0 < N)
    {w : Fin M → ℝ} (hw : FeasibleOuterWeight w) (z : BlockVec M N) :
    activationBranch w z ≤ hardValue z := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have houter := outerDot_le_positiveNorm (s := sigmaScore z) hw
  unfold activationBranch hardValue
  rw [activationNorm_eq_positiveNorm]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right houter _) (by positivity)

theorem activationBranch_canonical_eq_hardValue {M N : Nat}
    (z : BlockVec M N) :
    activationBranch (canonicalOuterWeight (sigmaScore z)) z = hardValue z := by
  unfold activationBranch hardValue
  rw [canonicalOuterWeight_dot, activationNorm_eq_positiveNorm]

end

end WeaklyConvexLowerBound

