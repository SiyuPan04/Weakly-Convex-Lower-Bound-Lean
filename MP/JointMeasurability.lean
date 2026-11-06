import MP.Family

/-! Joint Borel measurability of the genuine algorithm execution and
barrier event on the orthogonal-frame/private-seed probability space. -/

noncomputable section
namespace MP
open WC MeasureTheory
open WC.Rotation.Normalized

variable {d M N T : ℕ} [NeZero d]

theorem family_trajectory_measurable (H : Family d M N T) (A : WC.Model.BorelAlgorithm)
    (t : ℕ) : Measurable (show Orthogonal d × ℝ → Ambient d from fun p =>
      (WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        A (H.instanceOf p.1) p.2 t : Ambient d)) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      have heq : (show Orthogonal d × ℝ → Ambient d from fun p =>
          WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
            A (H.instanceOf p.1) p.2 0) = (fun _ => 0) := by
        funext p
        exact WC.Model.trajectory_zero _ _ _ _ _
      rw [heq]
      exact measurable_const
    | succ n =>
      have htranscript : Measurable (fun p : Orthogonal d × ℝ =>
          fun j : Fin (n + 1) => fullOracle (by norm_num : (0 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ≤ 1) (H.regularity p.1).lipschitz
            (H.regularity p.1).weaklyConvex
            (WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
              A (H.instanceOf p.1) p.2 j.val)) := by
        apply measurable_pi_lambda
        intro j
        exact H.measurable_oracle.comp (measurable_fst.prodMk (ih j.val j.isLt))
      have h := (A.measurable_decision_default d (n + 1)).comp
        (measurable_snd.prodMk htranscript)
      convert h using 1
      funext p
      rw [WC.Model.trajectory]
      rfl

theorem family_evaluatedOutput_measurable (H : Family d M N T) (A : WC.Model.BorelAlgorithm)
    (output : WC.Model.BorelOutputRule d T) :
    Measurable (show Orthogonal d × ℝ → Ambient d from fun p =>
      (WC.Model.evaluatedOutput (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        A (H.instanceOf p.1) output p.2 : Ambient d)) := by
  have htranscript : Measurable (fun p : Orthogonal d × ℝ =>
      fun j : Fin T => fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        (H.regularity p.1).lipschitz (H.regularity p.1).weaklyConvex
        (WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
          A (H.instanceOf p.1) p.2 j.val)) := by
    apply measurable_pi_lambda
    intro j
    exact H.measurable_oracle.comp
      (measurable_fst.prodMk (family_trajectory_measurable H A j.val))
  exact output.measurable_output_default.comp (measurable_snd.prodMk htranscript)

theorem family_barrierEvent_measurable (H : Family d M N T) (A : WC.Model.BorelAlgorithm)
    (output : WC.Model.BorelOutputRule d T) :
    MeasurableSet {p : Orthogonal d × ℝ | H.BarrierEvent A output p.1 p.2} := by
  have hquery (t : ℕ) : MeasurableSet {p : Orthogonal d × ℝ |
      1 / (32 * Real.sqrt (N : ℝ)) <
        ‖gradient (moreauEnvelope (1 / 2) (H.objective p.1))
          (WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
            A (H.instanceOf p.1) p.2 t)‖} :=
    measurableSet_lt measurable_const (H.measurable_gradient.comp
      (measurable_fst.prodMk (family_trajectory_measurable H A t))).norm
  have houtput : MeasurableSet {p : Orthogonal d × ℝ |
      1 / (32 * Real.sqrt (N : ℝ)) <
        ‖gradient (moreauEnvelope (1 / 2) (H.objective p.1))
          (WC.Model.evaluatedOutput (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
            A (H.instanceOf p.1) output p.2)‖} :=
    measurableSet_lt measurable_const (H.measurable_gradient.comp
      (measurable_fst.prodMk (family_evaluatedOutput_measurable H A output))).norm
  change MeasurableSet ({p : Orthogonal d × ℝ | ∀ t < T,
    1 / (32 * Real.sqrt (N : ℝ)) <
      ‖gradient (moreauEnvelope (1 / 2) (H.objective p.1))
        (WC.Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
          A (H.instanceOf p.1) p.2 t)‖} ∩ _)
  apply MeasurableSet.inter ?_ houtput
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ => hquery t

end MP
