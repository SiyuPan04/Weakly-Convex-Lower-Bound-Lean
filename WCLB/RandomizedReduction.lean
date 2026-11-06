import WCLB.Family
import WCLB.AdaptiveConcentration
import WCLB.Budget

/-! The exact logarithmic-dimension randomized reduction. Its event uses
the final objective's genuine Moreau gradient at actual queries and any
unqueried Borel output, under actual Haar × private-seed sampling. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace WCLB
open WC
open WC.Rotation.Normalized
set_option maxHeartbeats 800000

theorem barrier_of_strict_small {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) (hN : 256 ≤ N) (A : WC.Model.BorelAlgorithm)
    (out : WC.Model.BorelOutputRule d T) (g : Orthogonal d) (seed : ℝ)
    (good : ∀ c : Fin (T + 1), ‖H.candidate A out c (g, seed)‖ ≤ H.radius →
      ∀ j ∈ H.core, j ∉ H.candidateKnown c →
        |inner ℝ (coordinates g j) (H.candidate A out c (g, seed))| < H.tolerance) :
    H.BarrierEvent A out g seed := by
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    have hn : (256 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N : ℝ)]
  have hthreshold : 1 / (32 * Real.sqrt (N : ℝ)) < 1 := by
    apply (div_lt_one (by positivity : 0 < 32 * Real.sqrt (N : ℝ))).mpr
    linarith
  have hsim : ∀ c : Fin (T + 1), 1 / (32 * Real.sqrt N) <
      ‖gradient (moreauEnvelope (1 / 2) (H.objective g)) (H.candidate A out c (g, seed))‖ := by
    intro c
    by_cases hb : ‖H.candidate A out c (g, seed)‖ ≤ H.radius
    · apply H.terminal_barrier g _ hb
      intro i hicore hiterminal
      exact good c hb i hicore (fun hi => hiterminal (H.candidateKnown_terminal_subset c hi))
    · rw [(H.exterior g _ (lt_of_not_ge hb)).2]
      exact hthreshold
  have hsmall : ∀ t < T, ‖H.simulatedQuery A g seed t‖ ≤ H.radius →
      ∀ i ∈ H.core, i ∉ previous H.exposed t →
        |inner ℝ (coordinates g i) (H.simulatedQuery A g seed t)| < H.tolerance := by
    intro t ht hb i hicore hihidden
    let c : Fin (T + 1) := ⟨t, by omega⟩
    have hc : H.candidate A out c (g, seed) = H.simulatedQuery A g seed t := by
      simp [Family.candidate, c, ht]
    have hk : H.candidateKnown c = previous H.exposed t := by
      simp [Family.candidateKnown, c, ht]
    have h := good c (by rwa [hc]) i hicore (by rwa [hk])
    rwa [hc] at h
  constructor
  · intro t ht
    rw [H.coupling A g seed hsmall t ht.le]
    have h := hsim ⟨t, by omega⟩
    simpa [Family.candidate, ht] using h
  · rw [H.output_coupling A out g seed hsmall]
    have h := hsim ⟨T, by omega⟩
    simpa [Family.candidate] using h

theorem joint_barrier_of_exponential_budget {d M N T : ℕ} [NeZero d]
    (H : Family d M N T) (hN : 256 ≤ N) (A : WC.Model.BorelAlgorithm)
    (out : WC.Model.BorelOutputRule d T) (hdim : M * N + 1 ≤ d) (δ : ℝ≥0∞)
    (budget : (((T + 1) * (M * N) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (2 * Real.exp (-((d : ℝ) - (M * N : ℕ)) * H.tolerance ^ 2 /
        (2 * H.radius ^ 2))) ≤ δ) :
    1 - δ ≤ ((Frame.haar (Ambient d)).prod WC.Model.seedMeasure)
      {p | H.BarrierEvent A out p.1 p.2} := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let W : H.Test → Submodule ℝ (Ambient d) := fun i => H.candidateSpan i.val.1
  let v : ∀ i : H.Test, (W i)ᗮ := fun i =>
    FrameGeometry.hiddenVector b (H.candidateKnown i.val.1) i.val.2.val i.property
  let bad : H.Test → Set (Orthogonal d × ℝ) := fun i =>
    {p | ‖H.candidate A out i.val.1 p‖ ≤ H.radius ∧
      H.tolerance ≤ |inner ℝ (coordinates p.1 i.val.2.val) (H.candidate A out i.val.1 p)|}
  let q : ℝ := 2 * Real.exp (-((d : ℝ) - (M * N : ℕ)) * H.tolerance ^ 2 / (2 * H.radius ^ 2))
  have hdimreal : (0 : ℝ) < d - (M * N : ℕ) := by
    have hcast : ((M * N : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hdim
    linarith
  have hdimension (i : H.Test) : (d : ℝ) - (M * N : ℕ) ≤
      (Module.finrank ℝ (W i)ᗮ : ℝ) :=
    FrameGeometry.finrank_complement_ge_real b _ (H.candidateKnown_card i.val.1) (by omega)
  have hn (i : H.Test) : 0 < Module.finrank ℝ (W i)ᗮ := by
    have h := hdimension i
    by_contra hn
    have hz : Module.finrank ℝ (W i)ᗮ = 0 := by omega
    rw [hz] at h
    simp only [Nat.cast_zero] at h
    linarith
  have hmeas (i : H.Test) : MeasurableSet (bad i) := by
    have hc := H.candidate_measurable A out i.val.1
    have hcol : Measurable (fun p : Orthogonal d × ℝ => coordinates p.1 i.val.2.val) :=
      (Frame.continuous_column (Ambient d) (b i.val.2.val)).measurable.comp measurable_fst
    have hin : Measurable (fun p : Orthogonal d × ℝ =>
        |inner ℝ (coordinates p.1 i.val.2.val) (H.candidate A out i.val.1 p)|) := by fun_prop
    exact (measurableSet_le hc.norm measurable_const).inter
      (measurableSet_le measurable_const hin)
  have htail (i : H.Test) : ((Frame.haar (Ambient d)).prod WC.Model.seedMeasure) (bad i) ≤
      ENNReal.ofReal q := by
    letI : Nontrivial (W i)ᗮ := (Module.finrank_pos_iff (R := ℝ)).mp (hn i)
    have hraw := Concentration.adaptive_projection_tail_product (Ambient d) (W i)
      WC.Model.seedMeasure (hn i) (stdOrthonormalBasis ℝ (W i)ᗮ) (v i)
      (FrameGeometry.hiddenVector_unit b _ _ i.property)
      (H.candidate A out i.val.1) (H.candidate_measurable A out i.val.1)
      (fun s g h => H.candidate_fixed A out i.val.1 g s h)
      H.radius_positive H.tolerance_positive
    have hexp : 2 * Real.exp (-(Module.finrank ℝ (W i)ᗮ : ℝ) * H.tolerance ^ 2 /
        (2 * H.radius ^ 2)) ≤ q := by
      dsimp [q]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right (by have h := H.radius_positive; positivity : 0 < 2 * H.radius ^ 2)).mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (hdimension i)) (sq_nonneg _)
    exact hraw.trans (ENNReal.ofReal_le_ofReal hexp)
  have hbudget : ((Finset.univ : Finset H.Test).card : ℝ≥0∞) * ENNReal.ofReal q ≤ δ := by
    have hc : (Fintype.card H.Test : ℝ≥0∞) ≤ (((T + 1) * (M * N) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast H.test_card
    simpa only [Finset.card_univ] using (mul_le_mul_left hc (ENNReal.ofReal q)).trans budget
  have hg := Probability.simultaneous_good_probability
    ((Frame.haar (Ambient d)).prod WC.Model.seedMeasure) Finset.univ bad (ENNReal.ofReal q) δ
    (fun i _ => hmeas i) (fun i _ => htail i) hbudget
  apply hg.trans (measure_mono ?_)
  intro p hp
  apply barrier_of_strict_small H hN A out p.1 p.2
  intro c hb j hjcore hjhidden
  by_contra hbad
  apply hp
  exact Set.mem_iUnion.mpr ⟨⟨(c, ⟨j, hjcore⟩), hjhidden⟩,
    Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hb, le_of_not_gt hbad⟩⟩

/-- Lemma `lem:randomized-reduction` with the manuscript's exact radius,
tolerance and logarithmic ambient-dimension threshold. Uniform rectangular
frames are the indicated columns of an actual Haar orthogonal operator. -/
theorem randomized_reduction {M N d : ℕ} [NeZero d]
    (e : Fin M × Fin N ↪ Fin d) (hM : 2 ≤ M) (hN : 256 ≤ N)
    (hMmax : M ≤ 2 ^ (8 * N)) (A : WC.Model.BorelAlgorithm)
    (out : WC.Model.BorelOutputRule d ((M - 1) * stagger N))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : logarithmicDimensionBound (M * N) ((M - 1) * stagger N) d
      (radialRadius M N) (robustTolerance M N) δ) :
    ENNReal.ofReal (1 - δ) ≤ ((Frame.haar (Ambient d)).prod WC.Model.seedMeasure)
      {p | (chainFamily e hM hN hMmax).BarrierEvent A out p.1 p.2} := by
  let H := chainFamily e hM hN hMmax
  have hK : 0 < M * N := Nat.mul_pos (by omega) (by omega)
  have hd := logarithmic_dimension_positive hK hδ hδ1 hdim
  have hbudget := logarithmic_dimension_budget_ennreal hK
    (radialRadius_pos (N := N) (by omega)) (robustTolerance_pos M (by omega)) hδ hdim
  have hexp : -((d : ℝ) - (M * N : ℕ)) * (normalizedChainTolerance M N) ^ 2 /
      (2 * (4 * radialRadius M N) ^ 2) =
      -(9 * ((d : ℝ) - (M * N : ℕ)) * robustTolerance M N ^ 2) /
        (128 * radialRadius M N ^ 2) := by
    unfold normalizedChainTolerance
    ring
  have hh := joint_barrier_of_exponential_budget H hN A out hd (ENNReal.ofReal δ) (by
    change (((((M - 1) * stagger N + 1) * (M * N) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (2 * Real.exp (-((d : ℝ) - (M * N : ℕ)) *
        (normalizedChainTolerance M N) ^ 2 / (2 * (4 * radialRadius M N) ^ 2)))) ≤ _
    rw [hexp]
    exact hbudget)
  simpa only [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one] using hh

end WCLB
