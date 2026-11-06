import WC.GeneralRotation

/-! Physical scaling and fixed-instance complexity for general normalized
gap/threshold families, including the auxiliary convex chain. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WC.GeneralLowerReduction
open WC.LowerReduction
open WC.Rotation.General
open WC.Rotation.Normalized (Orthogonal)

theorem physical_barrier_transport {d K T : ℕ} [NeZero d]
    (H : Family d K T) {G ρ Δ : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hgap : (G ^ 2 / ρ) * H.gap ≤ Δ)
    (A : Model.BorelAlgorithm) {g : Orthogonal d} {seed : ℝ}
    (event : H.BarrierEvent (scaleAlgorithm G ρ A)
      (queryOutput (scaleAlgorithm G ρ A) d T) g seed) :
    ∀ t ≤ T, G * H.threshold <
      ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (physicalInstance hG hρ (H.instanceOf g) hgap).objective)
        (Model.trajectory hG.le hρ.le A (physicalInstance hG hρ (H.instanceOf g) hgap) seed t)‖ := by
  intro t ht
  have hb : H.threshold <
      ‖gradient (moreauEnvelope (1 / 2) (H.objective g))
        (Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
          (scaleAlgorithm G ρ A) (H.instanceOf g) seed t)‖ := by
    by_cases hlt : t < T
    · exact event.1 t hlt
    · have heq : t = T := by omega
      subst t
      have h := event.2
      erw [queryOutput_eq _ _ _ _ _ H.horizon_positive] at h
      exact h
  change G * H.threshold <
    ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (scaleFunction (G ^ 2 / ρ) (ρ / G) (H.objective g))) _‖
  rw [physical_moreau_gradient_norm hG hρ (H.regularity g)]
  erw [← trajectory_transport hG hρ A (H.instanceOf g) hgap seed t]
  exact mul_lt_mul_of_pos_left hb hG

theorem family_physical_hard_instance {d K T : ℕ} [NeZero d]
    (H : Family d K T) {G ρ Δ ε ν : ℝ} (hG : 0 < G) (hρ : 0 < ρ)
    (hν : 0 ≤ ν) (hν_one : ν < 1)
    (hgap : (G ^ 2 / ρ) * H.gap ≤ Δ) (hε : ε ≤ G * H.threshold)
    (hdim : K + 2 +
      ⌈4 * (K : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 /
        (((1 - ν) / 2) * H.tolerance ^ 2)⌉₊ ≤ d)
    (A : Model.BorelAlgorithm) :
    ∃ I : Model.Instance G ρ Δ, ∀ t ≤ T,
      Model.successProbability hG.le hρ.le A I ε t < ENNReal.ofReal (1 - ν) := by
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_one : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨g, hg⟩ := H.randomized_rotation (scaleAlgorithm G ρ A)
    (queryOutput (scaleAlgorithm G ρ A) d T) hδ hδ_one hdim
  let I := physicalInstance hG hρ (H.instanceOf g) hgap
  refine ⟨I, ?_⟩
  intro t ht
  have hsuccess : MeasurableSet {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (Model.trajectory hG.le hρ.le A I seed t)‖ ≤ ε} :=
    Model.stationarity_success_measurable hG.le hρ A I ε t
  have hdisjoint : {s | H.BarrierEvent (scaleAlgorithm G ρ A)
      (queryOutput (scaleAlgorithm G ρ A) d T) g s} ⊆
      {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
        (Model.trajectory hG.le hρ.le A I seed t)‖ ≤ ε}ᶜ := by
    intro seed hs
    have hb := physical_barrier_transport H hG hρ hgap A hs t ht
    intro hstationary
    exact (not_le_of_gt (hε.trans_lt hb)) hstationary
  have hprob := probability_le_of_disjoint_barrier Model.seedMeasure hsuccess hδ.le hδ_one.le hg hdisjoint
  have hstrict : ENNReal.ofReal δ < ENNReal.ofReal (1 - ν) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by dsimp [δ]; linarith)
  exact hprob.trans_lt hstrict

end WC.GeneralLowerReduction
