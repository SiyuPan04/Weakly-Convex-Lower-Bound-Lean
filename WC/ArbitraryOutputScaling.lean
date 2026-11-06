import WC.NormalizedFamily
import WC.GeneralLowerReduction

/-! Physical scaling for arbitrary Borel outputs formed from at most the
fixed transcript budget, including outputs that are never queried. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WC.LowerReduction
open WC.Rotation.Normalized

def scaleOutput (G ρ : ℝ) {d T : ℕ} (R : Model.BorelOutputRule d T) : Model.BorelOutputRule d T where
  output p := (ρ / G) • R.output (p.1, fun j => scaleReply (G ^ 2 / ρ) G (p.2 j))
  measurable_output := by
    apply measurable_to_borel
    have hreply : Measurable (fun p : ℝ × (Fin T → Model.Reply d) =>
        fun j => scaleReply (G ^ 2 / ρ) G (p.2 j)) := by
      apply measurable_pi_lambda
      intro j
      exact (scaleReply_continuous (E := Model.Space d) (G ^ 2 / ρ) G).measurable.comp
        ((measurable_pi_apply j).comp measurable_snd)
    exact (R.measurable_output_default.comp (measurable_fst.prodMk hreply)).const_smul (ρ / G)

theorem output_transport {G ρ Δ Δ' : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (A : Model.BorelAlgorithm) (I : Model.Instance 1 1 Δ) (hgap : (G ^ 2 / ρ) * Δ ≤ Δ')
    {T : ℕ} (R : Model.BorelOutputRule I.dimension T) (seed : ℝ) :
    Model.evaluatedOutput (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (scaleAlgorithm G ρ A) I (scaleOutput G ρ R) seed =
      (ρ / G) • Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ I hgap) R seed := by
  unfold Model.evaluatedOutput
  change (ρ / G) • R.output (_, _) = (ρ / G) • R.output (_, _)
  congr 1
  congr 1
  congr 1
  funext j
  dsimp only [Prod.fst, Prod.snd]
  rw [trajectory_transport hG hρ A I hgap seed j.val]
  exact (physical_fullOracle hG hρ I.admissible _).symm

theorem physical_arbitrary_output_barrier {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hgap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ)
    (A : Model.BorelAlgorithm) (R : Model.BorelOutputRule d T) {g : Orthogonal d} {seed : ℝ}
    (event : H.BarrierEvent (scaleAlgorithm G ρ A) (scaleOutput G ρ R) g seed) :
    G * (1 / (32 * Real.sqrt N)) <
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ := by
  change G * (1 / (32 * Real.sqrt N)) <
    ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (scaleFunction (G ^ 2 / ρ) (ρ / G) (H.objective g))) _‖
  rw [physical_moreau_gradient_norm hG hρ (H.regularity g)]
  erw [← output_transport hG hρ A (H.instanceOf g) hgap R seed]
  exact mul_lt_mul_of_pos_left event.2 hG

/-- The fixed physical hard instance defeats any prescribed Borel output
of the full seed and transcript. The frame is chosen before the seed. -/
theorem family_physical_arbitrary_output {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) (hN : 256 ≤ N)
    {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hgap : (G ^ 2 / ρ) * (3 * (M : ℝ) / N) ≤ Δ)
    (hε : ε ≤ G * (1 / (32 * Real.sqrt N)))
    (hdim : M * N + 2 +
      ⌈4 * (M * N : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 /
        (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d)
    (A : Model.BorelAlgorithm) (R : Model.BorelOutputRule d T) :
    ∃ g : Orthogonal d, Model.seedMeasure {seed |
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ ≤ ε}
        < ENNReal.ofReal (1 - ν) := by
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_one : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨g, hg⟩ := H.randomized_rotation hN (scaleAlgorithm G ρ A) (scaleOutput G ρ R) hδ hδ_one hdim
  refine ⟨g, ?_⟩
  have hsuccess := Model.arbitrary_output_success_measurable hG.le hρ A
    (physicalInstance hG hρ (H.instanceOf g) hgap) R ε
  have hdisjoint : {s | H.BarrierEvent (scaleAlgorithm G ρ A) (scaleOutput G ρ R) g s} ⊆
      {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ ≤ ε}ᶜ := by
    intro seed hs hstationary
    have hb := physical_arbitrary_output_barrier H hG hρ hgap A R hs
    exact (not_le_of_gt (hε.trans_lt hb)) hstationary
  have hprob := probability_le_of_disjoint_barrier Model.seedMeasure hsuccess hδ.le hδ_one.le hg hdisjoint
  have hstrict : ENNReal.ofReal δ < ENNReal.ofReal (1 - ν) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by dsimp [δ]; linarith)
  exact hprob.trans_lt hstrict

end WC.LowerReduction

namespace WC.GeneralLowerReduction
open WC.LowerReduction
open WC.Rotation.General
open WC.Rotation.Normalized (Orthogonal)

theorem physical_arbitrary_output_barrier {d K T : ℕ} [NeZero d]
    (H : Family d K T) {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hgap : (G ^ 2 / ρ) * H.gap ≤ Δ)
    (A : Model.BorelAlgorithm) (R : Model.BorelOutputRule d T) {g : Orthogonal d} {seed : ℝ}
    (event : H.BarrierEvent (scaleAlgorithm G ρ A) (scaleOutput G ρ R) g seed) :
    G * H.threshold <
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ := by
  change G * H.threshold < ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (scaleFunction (G ^ 2 / ρ) (ρ / G) (H.objective g))) _‖
  rw [physical_moreau_gradient_norm hG hρ (H.regularity g)]
  erw [← output_transport hG hρ A (H.instanceOf g) hgap R seed]
  exact mul_lt_mul_of_pos_left event.2 hG

theorem family_physical_arbitrary_output {d K T : ℕ} [NeZero d]
    (H : Family d K T) {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hgap : (G ^ 2 / ρ) * H.gap ≤ Δ) (hε : ε ≤ G * H.threshold)
    (hdim : K + 2 +
      ⌈4 * (K : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 /
        (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d)
    (A : Model.BorelAlgorithm) (R : Model.BorelOutputRule d T) :
    ∃ g : Orthogonal d, Model.seedMeasure {seed |
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ ≤ ε}
        < ENNReal.ofReal (1 - ν) := by
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_one : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨g, hg⟩ := H.randomized_rotation (scaleAlgorithm G ρ A) (scaleOutput G ρ R) hδ hδ_one hdim
  refine ⟨g, ?_⟩
  have hsuccess := Model.arbitrary_output_success_measurable hG.le hρ A
    (physicalInstance hG hρ (H.instanceOf g) hgap) R ε
  have hdisjoint : {s | H.BarrierEvent (scaleAlgorithm G ρ A) (scaleOutput G ρ R) g s} ⊆
      {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.evaluatedOutput hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) R seed)‖ ≤ ε}ᶜ := by
    intro seed hs hstationary
    have hb := physical_arbitrary_output_barrier H hG hρ hgap A R hs
    exact (not_le_of_gt (hε.trans_lt hb)) hstationary
  have hprob := probability_le_of_disjoint_barrier Model.seedMeasure hsuccess hδ.le hδ_one.le hg hdisjoint
  have hstrict : ENNReal.ofReal δ < ENNReal.ofReal (1 - ν) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by dsimp [δ]; linarith)
  exact hprob.trans_lt hstrict

end WC.GeneralLowerReduction
