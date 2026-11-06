import WC.Variational

/-! The actual compact convex parameter space of score weights. -/

noncomputable section
namespace WC

variable {ι : Type*} [Fintype ι]

theorem scoreWeights_nonempty : (scoreWeights (ι := ι)).Nonempty := by
  exact ⟨0, by simp [scoreWeights]⟩

theorem scoreWeights_isClosed : IsClosed (scoreWeights (ι := ι)) := by
  have horth : IsClosed {w : EuclideanSpace ℝ ι | ∀ i, 0 ≤ w i} := by
    have heq : {w : EuclideanSpace ℝ ι | ∀ i, 0 ≤ w i} =
        ⋂ i, {w : EuclideanSpace ℝ ι | 0 ≤ w i} := by ext w; simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i))
  exact horth.inter (isClosed_le continuous_norm continuous_const)

theorem scoreWeights_isCompact : IsCompact (scoreWeights (ι := ι)) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ ι) 1).of_isClosed_subset scoreWeights_isClosed
  intro w hw
  simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2

theorem scoreWeights_convex : Convex ℝ (scoreWeights (ι := ι)) := by
  intro w hw v hv a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * w i + b * v i
    exact add_nonneg (mul_nonneg ha (hw.1 i)) (mul_nonneg hb (hv.1 i))
  · have hnorm := norm_add_le (a • w) (b • v)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hnorm
    have ha' := mul_le_mul_of_nonneg_left hw.2 ha
    have hb' := mul_le_mul_of_nonneg_left hv.2 hb
    linarith

abbrev ScoreWeightSpace (M : ℕ) := (scoreWeights : Set (EuclideanSpace ℝ (Fin M)))

instance scoreWeightSpace_compactSpace (M : ℕ) : CompactSpace (ScoreWeightSpace M) :=
  isCompact_iff_compactSpace.mp scoreWeights_isCompact

instance scoreWeightSpace_nonempty (M : ℕ) : Nonempty (ScoreWeightSpace M) :=
  scoreWeights_nonempty.to_subtype

end WC
