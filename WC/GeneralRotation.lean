import WC.LowerReduction

/-! The proved rotation/simulation argument for an arbitrary unit-regular
family gap and barrier. This is used for the convex auxiliary chain. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WC.Rotation.General
open WC.Rotation.Normalized (Ambient Orthogonal coordinates Prefix framePrefix previous)
open WC.Rotation.Normalized (framePrefix_continuous measurable_from_borel)
set_option maxHeartbeats 400000
structure Family (d K T : ℕ) [NeZero d] where
  horizon_positive : 0 < T
  core : Finset (Fin d)
  core_card : core.card = K
  exposed : ℕ → Finset (Fin d)
  exposed_mono : Monotone exposed
  exposed_subset : ∀ t < T, exposed t ⊆ core
  exposed_proper : ∀ t < T, exposed t ≠ core
  width : ∀ t < T, (exposed t \ previous exposed t).card ≤ 5
  horizon_bound : K ≤ 16 * T
  radius : ℝ
  tolerance : ℝ
  radius_positive : 0 < radius
  tolerance_positive : 0 < tolerance
  gap : ℝ
  threshold : ℝ
  threshold_lt_one : threshold < 1
  objective : Orthogonal d → Ambient d → ℝ
  regularity : ∀ g, Admissible 1 1 gap (objective g)
  response : (t : ℕ) → Ambient d × Prefix (exposed t) → Model.Reply d
  measurable_response : ∀ t, @Measurable _ _ (borel _) (borel _) (response t)
  outside : Ambient d → Model.Reply d
  measurable_outside : @Measurable _ _ (borel _) (borel _) outside
  locality : ∀ t < T, ∀ g x, ‖x‖ ≤ radius →
    (∀ i ∈ core, i ∉ previous exposed t →
      |inner ℝ (coordinates g i) x| < tolerance) →
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (regularity g).lipschitz (regularity g).weaklyConvex x =
        response t (x, framePrefix (exposed t) g)
  terminal_barrier : ∀ g x, ‖x‖ ≤ radius →
    (∀ i ∈ core, i ∉ exposed (T - 1) →
      |inner ℝ (coordinates g i) x| < tolerance) →
    threshold < ‖gradient (moreauEnvelope (1 / 2) (objective g)) x‖
  exterior : ∀ g x, radius < ‖x‖ →
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (regularity g).lipschitz (regularity g).weaklyConvex x = outside x ∧
    ‖gradient (moreauEnvelope (1 / 2) (objective g)) x‖ = 1
  measurable_oracle : Measurable (fun p : Orthogonal d × Ambient d =>
    fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (regularity p.1).lipschitz (regularity p.1).weaklyConvex p.2)
  measurable_gradient : Measurable (fun p : Orthogonal d × Ambient d =>
    gradient (moreauEnvelope (1 / 2) (objective p.1)) p.2)

variable {d K T : ℕ} [NeZero d]

def Family.instanceOf (H : Family d K T) (g : Orthogonal d) :
    Model.Instance 1 1 H.gap :=
  ⟨d, H.objective g, H.regularity g⟩

/-- The globally defined simulated reply, even after an earlier failed test. -/
def Family.reply (H : Family d K T) (t : ℕ) (g : Orthogonal d)
    (x : Ambient d) : Model.Reply d :=
  if ‖x‖ ≤ H.radius then H.response t (x, framePrefix (H.exposed t) g) else H.outside x

def Family.simulatedQuery (H : Family d K T) (A : Model.BorelAlgorithm)
    (g : Orthogonal d) (seed : ℝ) (t : ℕ) : Ambient d :=
  match t with
  | 0 => 0
  | n + 1 => A.decision d (n + 1) (seed, fun j : Fin (n + 1) =>
      H.reply j g (H.simulatedQuery A g seed j))
termination_by t
decreasing_by exact j.isLt

def Family.simulatedOutput (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (g : Orthogonal d) (seed : ℝ) : Ambient d :=
  output.output (seed, fun j : Fin T => H.reply j g (H.simulatedQuery A g seed j))

theorem Family.previous_subset (H : Family d K T) {t s : ℕ} (ht : t ≤ s + 1) :
    previous H.exposed t ⊆ H.exposed s := by
  cases t with
  | zero => simp [previous]
  | succ t => exact H.exposed_mono (Nat.le_of_succ_le_succ ht)

theorem Family.reply_eq_oracle (H : Family d K T) {t : ℕ} (ht : t < T)
    (g : Orthogonal d) (x : Ambient d)
    (small : ‖x‖ ≤ H.radius → ∀ i ∈ H.core, i ∉ previous H.exposed t →
      |inner ℝ (coordinates g i) x| < H.tolerance) :
    H.reply t g x = fullOracle (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      (H.regularity g).lipschitz (H.regularity g).weaklyConvex x := by
  unfold Family.reply
  split_ifs with hb
  · exact (H.locality t ht g x hb (small hb)).symm
  · exact (H.exterior g x (lt_of_not_ge hb)).1.symm

/-- Prefix dependence of the simulation is proved by induction, not
assumed as a probabilistic independence assertion. -/
theorem Family.simulatedQuery_prefix (H : Family d K T) (A : Model.BorelAlgorithm)
    (t : ℕ) (g g' : Orthogonal d) (seed : ℝ)
    (same : ∀ i ∈ previous H.exposed t, coordinates g i = coordinates g' i) :
    H.simulatedQuery A g seed t = H.simulatedQuery A g' seed t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => rw [Family.simulatedQuery, Family.simulatedQuery]
    | succ n =>
      rw [Family.simulatedQuery, Family.simulatedQuery]
      congr 1
      congr 1
      funext j
      have hquery : H.simulatedQuery A g seed j = H.simulatedQuery A g' seed j :=
        ih j j.isLt (fun i hi => same i (H.previous_subset (Nat.le_of_lt j.isLt) hi))
      rw [hquery]
      unfold Family.reply
      have hprefix : framePrefix (H.exposed j) g = framePrefix (H.exposed j) g' := by
        apply Subtype.ext
        funext i
        exact same i.val (H.exposed_mono (Nat.le_of_lt_succ j.isLt) i.property)
      rw [hprefix]

omit [NeZero d] in
theorem framePrefix_continuous (I : Finset (Fin d)) : Continuous (framePrefix I) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun i => Frame.continuous_column (Ambient d)
    (EuclideanSpace.basisFun (Fin d) ℝ i.val))

theorem measurable_from_borel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (h : @Measurable X Y (borel X) (borel Y) f) : Measurable f :=
  h.mono (le_of_eq BorelSpace.measurable_eq.symm) (le_of_eq BorelSpace.measurable_eq)

theorem Family.reply_measurable (H : Family d K T) (t : ℕ) :
    Measurable (fun p : Orthogonal d × Ambient d => H.reply t p.1 p.2) := by
  unfold Family.reply
  have hin : Measurable (fun p : Orthogonal d × Ambient d =>
      H.response t (p.2, framePrefix (H.exposed t) p.1)) :=
    (measurable_from_borel (H.measurable_response t)).comp
      (measurable_snd.prodMk ((framePrefix_continuous (H.exposed t)).measurable.comp measurable_fst))
  have hout : Measurable (fun p : Orthogonal d × Ambient d => H.outside p.2) :=
    (measurable_from_borel H.measurable_outside).comp measurable_snd
  have hcondition : MeasurableSet {p : Orthogonal d × Ambient d | ‖p.2‖ ≤ H.radius} :=
    measurableSet_le measurable_snd.norm measurable_const
  exact hin.ite hcondition hout

theorem Family.reply_comp_measurable (H : Family d K T) (t : ℕ)
    (q : Orthogonal d × ℝ → Ambient d) (hq : Measurable q) :
    Measurable (fun p : Orthogonal d × ℝ => H.reply t p.1 (q p)) := by
  unfold Family.reply
  have hin : Measurable (fun p : Orthogonal d × ℝ =>
      H.response t (q p, framePrefix (H.exposed t) p.1)) :=
    (measurable_from_borel (H.measurable_response t)).comp
      (hq.prodMk ((framePrefix_continuous (H.exposed t)).measurable.comp measurable_fst))
  have hout : Measurable (fun p : Orthogonal d × ℝ => H.outside (q p)) :=
    (measurable_from_borel H.measurable_outside).comp hq
  have hcondition : MeasurableSet {p : Orthogonal d × ℝ | ‖q p‖ ≤ H.radius} :=
    measurableSet_le hq.norm measurable_const
  exact hin.ite hcondition hout

theorem Family.simulatedQuery_measurable (H : Family d K T) (A : Model.BorelAlgorithm)
    (t : ℕ) : Measurable (fun p : Orthogonal d × ℝ => H.simulatedQuery A p.1 p.2 t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simpa only [Family.simulatedQuery] using
        (measurable_const : Measurable (fun _ : Orthogonal d × ℝ => (0 : Ambient d)))
    | succ n =>
      have heq : (fun p : Orthogonal d × ℝ => H.simulatedQuery A p.1 p.2 (n + 1)) =
          (fun p => A.decision d (n + 1)
            (p.2, fun j : Fin (n + 1) => H.reply j.val p.1 (H.simulatedQuery A p.1 p.2 j.val))) := by
        funext p
        rw [Family.simulatedQuery]
      rw [heq]
      have htranscript : Measurable (fun p : Orthogonal d × ℝ =>
          fun j : Fin (n + 1) => H.reply j p.1 (H.simulatedQuery A p.1 p.2 j)) := by
        apply measurable_pi_lambda
        intro j
        exact H.reply_comp_measurable j.val
          (fun p => H.simulatedQuery A p.1 p.2 j.val) (ih j.val j.isLt)
      have hcomp := (A.measurable_decision_default d (n + 1)).comp
        (measurable_snd.prodMk htranscript)
      exact hcomp

theorem Family.simulatedOutput_measurable (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) :
    Measurable (fun p : Orthogonal d × ℝ => H.simulatedOutput A output p.1 p.2) := by
  unfold Family.simulatedOutput
  have htranscript : Measurable (fun p : Orthogonal d × ℝ =>
      fun j : Fin T => H.reply j.val p.1 (H.simulatedQuery A p.1 p.2 j.val)) := by
    apply measurable_pi_lambda
    intro j
    exact H.reply_comp_measurable j.val
      (fun p => H.simulatedQuery A p.1 p.2 j.val) (H.simulatedQuery_measurable A j.val)
  exact output.measurable_output_default.comp (measurable_snd.prodMk htranscript)

theorem Family.simulatedOutput_prefix (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (g g' : Orthogonal d) (seed : ℝ)
    (same : ∀ i ∈ H.exposed (T - 1), coordinates g i = coordinates g' i) :
    H.simulatedOutput A output g seed = H.simulatedOutput A output g' seed := by
  unfold Family.simulatedOutput
  congr 1
  congr 1
  funext j
  have hquery : H.simulatedQuery A g seed j = H.simulatedQuery A g' seed j :=
    H.simulatedQuery_prefix A j g g' seed
      (fun i hi => same i (H.previous_subset (by omega : j.val ≤ (T - 1) + 1) hi))
  rw [hquery]
  unfold Family.reply
  have hp : framePrefix (H.exposed j) g = framePrefix (H.exposed j) g' := by
    apply Subtype.ext
    funext i
    exact same i.val (H.exposed_mono (by omega : j.val ≤ T - 1) i.property)
  rw [hp]

/-- Equality of actual and simulated queries on a successful projection
event. This is the real oracle coupling induction for the exact model. -/
theorem Family.coupling (H : Family d K T) (A : Model.BorelAlgorithm)
    (g : Orthogonal d) (seed : ℝ)
    (good : ∀ t < T, ‖H.simulatedQuery A g seed t‖ ≤ H.radius →
      ∀ i ∈ H.core, i ∉ previous H.exposed t →
        |inner ℝ (coordinates g i) (H.simulatedQuery A g seed t)| < H.tolerance) :
    ∀ t ≤ T, Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      A (H.instanceOf g) seed t = H.simulatedQuery A g seed t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    cases t with
    | zero => rw [Model.trajectory, Family.simulatedQuery]
              rfl
    | succ n =>
      rw [Model.trajectory, Family.simulatedQuery]
      congr 1
      congr 1
      funext j
      have hquery := ih j j.isLt (by omega : j.val ≤ T)
      rw [hquery]
      exact (H.reply_eq_oracle (by omega : j.val < T) g _ (good j (by omega))).symm

theorem Family.output_coupling (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (g : Orthogonal d) (seed : ℝ)
    (good : ∀ t < T, ‖H.simulatedQuery A g seed t‖ ≤ H.radius →
      ∀ i ∈ H.core, i ∉ previous H.exposed t →
        |inner ℝ (coordinates g i) (H.simulatedQuery A g seed t)| < H.tolerance) :
    Model.evaluatedOutput (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      A (H.instanceOf g) output seed = H.simulatedOutput A output g seed := by
  unfold Model.evaluatedOutput Family.simulatedOutput
  congr 1
  congr 1
  funext j
  rw [H.coupling A g seed good j (le_of_lt j.isLt)]
  exact (H.reply_eq_oracle j.isLt g _ (good j j.isLt)).symm

/-- The first `T` queries and the arbitrary output are treated as `T+1`
candidates, each with exactly the information exposed before it is formed. -/
def Family.candidateKnown (H : Family d K T) (c : Fin (T + 1)) : Finset (Fin d) :=
  if c.val < T then previous H.exposed c.val else H.exposed (T - 1)

def Family.candidate (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (c : Fin (T + 1)) (p : Orthogonal d × ℝ) : Ambient d :=
  if c.val < T then H.simulatedQuery A p.1 p.2 c.val else H.simulatedOutput A output p.1 p.2

theorem Family.candidate_measurable (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (c : Fin (T + 1)) : Measurable (H.candidate A output c) := by
  unfold Family.candidate
  split_ifs
  · exact H.simulatedQuery_measurable A c.val
  · exact H.simulatedOutput_measurable A output

theorem Family.candidateKnown_subset (H : Family d K T) (c : Fin (T + 1)) :
    H.candidateKnown c ⊆ H.core := by
  unfold Family.candidateKnown
  split_ifs with hc
  · cases hn : c.val with
    | zero => simp [previous]
    | succ n => exact H.exposed_subset n (by omega)
  · exact H.exposed_subset (T - 1) (by have := H.horizon_positive; omega)

theorem Family.candidateKnown_card (H : Family d K T) (c : Fin (T + 1)) :
    (H.candidateKnown c).card ≤ K := by
  exact (Finset.card_le_card (H.candidateKnown_subset c)).trans_eq H.core_card

theorem Family.candidate_prefix (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (c : Fin (T + 1))
    (g g' : Orthogonal d) (seed : ℝ)
    (same : ∀ i ∈ H.candidateKnown c, coordinates g i = coordinates g' i) :
    H.candidate A output c (g, seed) = H.candidate A output c (g', seed) := by
  unfold Family.candidate Family.candidateKnown at *
  split_ifs with hc
  · apply H.simulatedQuery_prefix A c.val g g' seed
    simpa only [if_pos hc] using same
  · apply H.simulatedOutput_prefix A output g g' seed
    simpa only [if_neg hc] using same

def Family.candidateSpan (H : Family d K T) (c : Fin (T + 1)) : Submodule ℝ (Ambient d) :=
  FrameGeometry.exposedSpan (EuclideanSpace.basisFun (Fin d) ℝ) (H.candidateKnown c)

theorem Family.candidate_fixed (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (c : Fin (T + 1))
    (g : Orthogonal d) (seed : ℝ) (h : Frame.Orthogonal (H.candidateSpan c)ᗮ) :
    H.candidate A output c (g * Frame.embed (Ambient d) (H.candidateSpan c) h, seed) =
      H.candidate A output c (g, seed) := by
  apply H.candidate_prefix A output c _ g seed
  intro i hi
  have hmem : EuclideanSpace.basisFun (Fin d) ℝ i ∈ H.candidateSpan c :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  change Frame.act (Ambient d) (g * Frame.embed (Ambient d) (H.candidateSpan c) h)
      (EuclideanSpace.basisFun (Fin d) ℝ i) = _
  rw [Frame.act_mul]
  have he := Frame.embed_apply_exposed (Ambient d) (H.candidateSpan c) h
    ⟨EuclideanSpace.basisFun (Fin d) ℝ i, hmem⟩
  rw [he]
  rfl

/-- Exactly the hidden coordinate tests; revealed coordinates do not need
a test and cannot increase the count beyond `(T+1)MN`. -/
abbrev Family.Test (H : Family d K T) :=
  {p : Fin (T + 1) × {j : Fin d // j ∈ H.core} // p.2.val ∉ H.candidateKnown p.1}

instance Family.test_fintype (H : Family d K T) : Fintype H.Test := Fintype.ofFinite _

theorem Family.test_card (H : Family d K T) : Fintype.card H.Test ≤ (T + 1) * (K) := by
  have h := Fintype.card_le_of_injective
    (fun i : H.Test => i.val) Subtype.val_injective
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, H.core_card] at h
  exact h

def Family.SmallCandidateEvent (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (g : Orthogonal d) (seed : ℝ) : Prop :=
  ∀ c : Fin (T + 1), ‖H.candidate A output c (g, seed)‖ ≤ H.radius →
    ∀ j ∈ H.core, j ∉ H.candidateKnown c →
      |inner ℝ (coordinates g j) (H.candidate A output c (g, seed))| ≤ H.tolerance / 2

/-- The actual fixed-frame small-projection conclusion for every Borel
algorithm and arbitrary Borel output in the exact oracle model. -/
theorem Family.exists_fixed_frame_candidates (H : Family d K T)
    (A : Model.BorelAlgorithm) (output : Model.BorelOutputRule d T)
    (hdim : K + 2 ≤ d) (δ : ℝ≥0∞)
    (budget : (((T + 1) * (K) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (4 * H.radius ^ 2 / (((d : ℝ) - (K : ℕ)) * H.tolerance ^ 2)) ≤ δ) :
    ∃ g : Orthogonal d, 1 - δ ≤ Model.seedMeasure {s | H.SmallCandidateEvent A output g s} := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let W : H.Test → Submodule ℝ (Ambient d) := fun i => H.candidateSpan i.val.1
  let v : ∀ i : H.Test, (W i)ᗮ := fun i =>
    FrameGeometry.hiddenVector b (H.candidateKnown i.val.1) i.val.2.val i.property
  have hnontrivial (i : H.Test) : Nontrivial (W i)ᗮ :=
    FrameGeometry.complement_nontrivial b _ (H.candidateKnown_card i.val.1) hdim
  have hunit (i : H.Test) : ‖v i‖ = 1 :=
    FrameGeometry.hiddenVector_unit b _ _ i.property
  have hL : 0 < (d : ℝ) - (K : ℕ) := by
    have hlt : ((K : ℕ) : ℝ) < d := by exact_mod_cast (show K < d by omega)
    linarith
  have hdimension (i : H.Test) : (d : ℝ) - (K : ℕ) ≤ (Module.finrank ℝ (W i)ᗮ : ℝ) :=
    FrameGeometry.finrank_complement_ge_real b _ (H.candidateKnown_card i.val.1) (by omega)
  have hcard : (Fintype.card H.Test : ℝ≥0∞) ≤ (((T + 1) * (K) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast H.test_card
  have hbudget := (mul_le_mul_left hcard
    (ENNReal.ofReal (4 * H.radius ^ 2 / (((d : ℝ) - (K : ℕ)) * H.tolerance ^ 2)))).trans budget
  obtain ⟨g, hg⟩ := exists_fixed_frame_small_projections Model.seedMeasure W hnontrivial v hunit
    (fun i => H.candidate A output i.val.1) (fun i => H.candidate_measurable A output i.val.1)
    (fun i s g h => H.candidate_fixed A output i.val.1 g s h)
    H.radius_positive.le H.tolerance_positive hL hdimension δ hbudget
  refine ⟨g, ?_⟩
  have heq : {s | ∀ i : H.Test, ‖H.candidate A output i.val.1 (g, s)‖ ≤ H.radius →
        |inner ℝ (Frame.act (Ambient d) g (v i : Ambient d))
          (H.candidate A output i.val.1 (g, s))| ≤ H.tolerance / 2} =
      {s | H.SmallCandidateEvent A output g s} := by
    ext s
    constructor
    · intro hs c hc j hjcore hjhidden
      exact hs ⟨(c, ⟨j, hjcore⟩), hjhidden⟩ hc
    · intro hs i hi
      exact hs i.val.1 hi i.val.2.val i.val.2.property i.property
  rw [heq] at hg
  exact hg

theorem Family.candidateKnown_terminal_subset (H : Family d K T) (c : Fin (T + 1)) :
    H.candidateKnown c ⊆ H.exposed (T - 1) := by
  unfold Family.candidateKnown
  split_ifs with hc
  · exact H.previous_subset (by omega : c.val ≤ (T - 1) + 1)
  · exact Finset.Subset.refl _

theorem Family.small_event_query (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) {g : Orthogonal d} {seed : ℝ}
    (good : H.SmallCandidateEvent A output g seed) {t : ℕ} (ht : t < T)
    (hb : ‖H.simulatedQuery A g seed t‖ ≤ H.radius) :
    ∀ i ∈ H.core, i ∉ previous H.exposed t →
      |inner ℝ (coordinates g i) (H.simulatedQuery A g seed t)| < H.tolerance := by
  intro i hicore hihidden
  let c : Fin (T + 1) := ⟨t, by omega⟩
  have hcand : H.candidate A output c (g, seed) = H.simulatedQuery A g seed t := by
    simp [Family.candidate, c, ht]
  have hknown : H.candidateKnown c = previous H.exposed t := by
    simp [Family.candidateKnown, c, ht]
  have hs := good c (by rwa [hcand]) i hicore (by rwa [hknown])
  rw [hcand] at hs
  exact hs.trans_lt (by have := H.tolerance_positive; linarith)

def Family.BarrierEvent (H : Family d K T) (A : Model.BorelAlgorithm)
    (output : Model.BorelOutputRule d T) (g : Orthogonal d) (seed : ℝ) : Prop :=
  (∀ t < T, H.threshold <
    ‖gradient (moreauEnvelope (1 / 2) (H.objective g))
      (Model.trajectory (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        A (H.instanceOf g) seed t)‖) ∧
  H.threshold <
    ‖gradient (moreauEnvelope (1 / 2) (H.objective g))
      (Model.evaluatedOutput (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
        A (H.instanceOf g) output seed)‖

/-- The small-projection event forces the strict barrier for all actual
queries and for the arbitrary output. Both branches refer to the final
function's own Moreau envelope. -/
theorem Family.small_event_barrier (H : Family d K T)
    (A : Model.BorelAlgorithm) (output : Model.BorelOutputRule d T)
    {g : Orthogonal d} {seed : ℝ} (good : H.SmallCandidateEvent A output g seed) :
    H.BarrierEvent A output g seed := by
  have hthreshold := H.threshold_lt_one
  have hsim : ∀ c : Fin (T + 1), H.threshold <
      ‖gradient (moreauEnvelope (1 / 2) (H.objective g)) (H.candidate A output c (g, seed))‖ := by
    intro c
    by_cases hb : ‖H.candidate A output c (g, seed)‖ ≤ H.radius
    · apply H.terminal_barrier g _ hb
      intro i hicore hterminal
      have hi : i ∉ H.candidateKnown c := fun h => hterminal (H.candidateKnown_terminal_subset c h)
      exact (good c hb i hicore hi).trans_lt (by have := H.tolerance_positive; linarith)
    · rw [(H.exterior g _ (lt_of_not_ge hb)).2]
      exact hthreshold
  have hsmall : ∀ t < T, ‖H.simulatedQuery A g seed t‖ ≤ H.radius →
      ∀ i ∈ H.core, i ∉ previous H.exposed t →
        |inner ℝ (coordinates g i) (H.simulatedQuery A g seed t)| < H.tolerance :=
    fun _ ht => H.small_event_query A output good ht
  constructor
  · intro t ht
    rw [H.coupling A g seed hsmall t ht.le]
    have h := hsim ⟨t, by omega⟩
    simpa [Family.candidate, ht] using h
  · rw [H.output_coupling A output g seed hsmall]
    have h := hsim ⟨T, by omega⟩
    simpa [Family.candidate] using h

/-- The abstract randomized rotation theorem with an explicit probability
budget. No random-frame law is assumed: Haar sampling, adaptive tests,
coupling, and fixed-frame extraction have all been proved above. -/
theorem Family.randomized_rotation_of_budget (H : Family d K T)
    (A : Model.BorelAlgorithm) (output : Model.BorelOutputRule d T)
    (hdim : K + 2 ≤ d) (δ : ℝ≥0∞)
    (budget : (((T + 1) * (K) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (4 * H.radius ^ 2 / (((d : ℝ) - (K : ℕ)) * H.tolerance ^ 2)) ≤ δ) :
    ∃ g : Orthogonal d, 1 - δ ≤ Model.seedMeasure {s | H.BarrierEvent A output g s} := by
  obtain ⟨g, hg⟩ := H.exists_fixed_frame_candidates A output hdim δ budget
  refine ⟨g, hg.trans (measure_mono ?_)⟩
  exact fun s hs => H.small_event_barrier A output hs

/-- The manuscript's exact sufficient ambient dimension, including the
unqueried arbitrary output and all unrestricted exterior queries. -/
theorem Family.randomized_rotation (H : Family d K T)
    (A : Model.BorelAlgorithm) (output : Model.BorelOutputRule d T)
    {δ : ℝ} (hδ : 0 < δ) (_hδ_one : δ < 1)
    (hdim : K + 2 +
      ⌈4 * (K : ℕ) * (T + 1 : ℝ) * H.radius ^ 2 / (δ * H.tolerance ^ 2)⌉₊ ≤ d) :
    ∃ g : Orthogonal d, ENNReal.ofReal (1 - δ) ≤
      Model.seedMeasure {s | H.BarrierEvent A output g s} := by
  have hbudget := rotation_dimension_budget_ennreal H.tolerance_positive hδ hdim
  have hcount : ENNReal.ofReal ((K : ℕ) * (T + 1 : ℝ)) =
      (((T + 1) * (K) : ℕ) : ℝ≥0∞) := by
    rw [show ((K : ℕ) : ℝ) * (T + 1 : ℝ) =
      (((T + 1) * (K) : ℕ) : ℝ) by push_cast; ring]
    exact ENNReal.ofReal_natCast _
  rw [hcount] at hbudget
  obtain ⟨g, hg⟩ := H.randomized_rotation_of_budget A output (by omega)
    (ENNReal.ofReal δ) hbudget
  refine ⟨g, ?_⟩
  simpa [ENNReal.ofReal_sub 1 (le_of_lt hδ)] using hg


end WC.Rotation.General

