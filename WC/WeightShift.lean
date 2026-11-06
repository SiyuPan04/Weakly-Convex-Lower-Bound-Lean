import WC.CoupledRegularity

noncomputable section
namespace WC

open scoped BigOperators

def nextWeights {M : ℕ} (w : EuclideanSpace ℝ (Fin M)) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (nextWeight w)

theorem nextWeights_norm_le {M : ℕ} (w : EuclideanSpace ℝ (Fin M)) :
    ‖nextWeights w‖ ≤ ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  cases M with
  | zero => simp
  | succ M =>
    have hl : (∑ m : Fin (M + 1), nextWeights w m ^ 2) =
        ∑ m : Fin M, w m.succ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp only [nextWeights, PiLp.toLp_apply, nextWeight_castSucc, nextWeight_last,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [hl, Fin.sum_univ_succ]
    nlinarith [sq_nonneg (w 0)]

theorem nextWeights_mem_scoreWeights {M : ℕ} {w : EuclideanSpace ℝ (Fin M)}
    (hw : w ∈ scoreWeights) : nextWeights w ∈ scoreWeights :=
  ⟨nextWeight_nonneg hw, (nextWeights_norm_le w).trans hw.2⟩

end WC
