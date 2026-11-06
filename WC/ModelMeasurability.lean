import WC.Model

/-!
# Measurability of the actual oracle trajectories and stationarity events
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem proximalPoint_lipschitzWith [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) : LipschitzWith 2 (proximalPoint ρ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := proximal_displacement_lipschitz hρ hwc
    (proximalPoint_spec hρ hG hlip y) (proximalPoint_spec hρ hG hlip x)
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using h

theorem moreau_gradient_continuous [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) :
    Continuous (gradient (moreauEnvelope (1 / (2 * ρ)) f)) := by
  have heq : gradient (moreauEnvelope (1 / (2 * ρ)) f) =
      fun x => (2 * ρ) • (x - proximalPoint ρ f x) :=
    funext (moreau_gradient_eq hρ hG hlip hwc)
  rw [heq]
  exact continuous_const.smul
    (continuous_id.sub (proximalPoint_lipschitzWith hG hρ hlip hwc).continuous)

theorem moreau_gradient_norm_sub_le [ProperSpace E] {G ρ : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hlip : GloballyLipschitz G f)
    (hwc : WeaklyConvex ρ f) (x y : E) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) x -
      gradient (moreauEnvelope (1 / (2 * ρ)) f) y‖ ≤ 6 * ρ * ‖x - y‖ := by
  rw [moreau_gradient_eq hρ hG hlip hwc, moreau_gradient_eq hρ hG hlip hwc,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * ρ by positivity)]
  have heq : (x - proximalPoint ρ f x) - (y - proximalPoint ρ f y) =
      (x - y) - (proximalPoint ρ f x - proximalPoint ρ f y) := by module
  rw [heq]
  have ht := norm_sub_le (x - y) (proximalPoint ρ f x - proximalPoint ρ f y)
  have hp := proximal_displacement_lipschitz hρ hwc
    (proximalPoint_spec hρ hG hlip y) (proximalPoint_spec hρ hG hlip x)
  nlinarith

namespace Model

open MeasureTheory

instance space_measurableSpace (d : ℕ) : MeasurableSpace (Space d) := borel _
instance space_borelSpace (d : ℕ) : BorelSpace (Space d) := ⟨rfl⟩

theorem BorelAlgorithm.measurable_decision_default (A : BorelAlgorithm) (d t : ℕ) :
    Measurable (A.decision d t) := by
  have hsrc : (inferInstance : MeasurableSpace (ℝ × (Fin t → Reply d))) =
      borel (ℝ × (Fin t → Reply d)) := BorelSpace.measurable_eq
  exact (A.measurable_decision d t).mono (le_of_eq hsrc.symm) le_rfl

/-- Every finite trajectory coordinate is genuinely measurable in the private seed. -/
theorem trajectory_measurable {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (t : ℕ) :
    Measurable (fun seed => trajectory hG hρ A I seed t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simpa only [trajectory_zero] using (measurable_const : Measurable (fun _ : ℝ => (0 : Space I.dimension)))
    | succ n =>
      have htranscript : Measurable (fun seed : ℝ => fun s : Fin (n + 1) =>
          fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
            (trajectory hG hρ A I seed s.val)) := by
        apply measurable_pi_lambda
        intro s
        exact (fullOracle_measurable hG hρ I.admissible.lipschitz I.admissible.weaklyConvex).comp
          (ih s.val s.isLt)
      have hcomp := (A.measurable_decision_default I.dimension (n + 1)).comp
        (measurable_id.prodMk htranscript)
      convert hcomp using 1
      funext seed
      rw [trajectory]
      rfl

theorem stationarity_success_measurable {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 < ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (ε : ℝ) (t : ℕ) :
    MeasurableSet {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (trajectory hG hρ.le A I seed t)‖ ≤ ε} := by
  have hgrad := (moreau_gradient_continuous hG hρ I.admissible.lipschitz
    I.admissible.weaklyConvex).measurable
  exact measurableSet_le (hgrad.comp (trajectory_measurable hG hρ.le A I t) |>.norm)
    measurable_const

theorem BorelOutputRule.measurable_output_default {d T : ℕ} (R : BorelOutputRule d T) :
    Measurable R.output := by
  have hsrc : (inferInstance : MeasurableSpace (ℝ × (Fin T → Reply d))) =
      borel (ℝ × (Fin T → Reply d)) := BorelSpace.measurable_eq
  exact R.measurable_output.mono (le_of_eq hsrc.symm) le_rfl

/-- Evaluate an arbitrary fixed-horizon output rule on the actual transcript. -/
def evaluatedOutput {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) {T : ℕ}
    (R : BorelOutputRule I.dimension T) (seed : ℝ) : Space I.dimension :=
  R.output (seed, fun s : Fin T => fullOracle hG hρ I.admissible.lipschitz
    I.admissible.weaklyConvex (trajectory hG hρ A I seed s.val))

theorem evaluatedOutput_measurable {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) {T : ℕ}
    (R : BorelOutputRule I.dimension T) : Measurable (evaluatedOutput hG hρ A I R) := by
  apply R.measurable_output_default.comp
  apply measurable_id.prodMk
  apply measurable_pi_lambda
  intro s
  exact (fullOracle_measurable hG hρ I.admissible.lipschitz I.admissible.weaklyConvex).comp
    (trajectory_measurable hG hρ A I s.val)

theorem arbitrary_output_success_measurable {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 < ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) {T : ℕ}
    (R : BorelOutputRule I.dimension T) (ε : ℝ) :
    MeasurableSet {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (evaluatedOutput hG hρ.le A I R seed)‖ ≤ ε} := by
  have hgrad := (moreau_gradient_continuous hG hρ I.admissible.lipschitz
    I.admissible.weaklyConvex).measurable
  exact measurableSet_le (hgrad.comp (evaluatedOutput_measurable hG hρ.le A I R) |>.norm)
    measurable_const

end Model
end WC
