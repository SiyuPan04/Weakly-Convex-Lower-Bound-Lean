import WC.OuterConvergence
import WC.MinNormSelection
import WC.ModelMeasurability

/-! A genuine deterministic exact-oracle algorithm in the manuscript's Borel model. -/

noncomputable section
namespace WC
namespace UpperModel

open scoped BigOperators ENNReal

abbrev State (E : Type*) := E × E × E
abbrev OracleReply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := ℝ × CompactConvexSets E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finish (ρ ε : ℝ) (L : ℕ) (x s : E) : State E :=
  let y := (2 / ((L : ℝ) * (L + 1))) • s
  let c := if ‖y - x‖ ≤ ε / (4 * ρ) then x else y
  (c, c, 0)

def step (ρ G ε : ℝ) (L k : ℕ) (s : State E) (reply : OracleReply E) : State E :=
  let j := k % L + 1
  let total := s.2.2 + (j : ℝ) • s.2.1
  if j = L then finish ρ ε L s.1 total else
    (s.1, proximalSubgradientStep s.1 ρ G (2 / (ρ * ((j : ℝ) + 1)))
      s.2.1 (minimumNormReply reply), total)

def replay (ρ G ε : ℝ) (L : ℕ) : (t : ℕ) → (Fin t → OracleReply E) → State E
  | 0, _ => (0, 0, 0)
  | k + 1, replies => step ρ G ε L k
      (replay ρ G ε L k (fun j => replies j.castSucc)) (replies (Fin.last k))

theorem finish_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ ε : ℝ) (L : ℕ) : Measurable (fun p : E × E => finish ρ ε L p.1 p.2) := by
  unfold finish
  have hy : Measurable (fun p : E × E => (2 / ((L : ℝ) * (L + 1))) • p.2) :=
    measurable_const.smul measurable_snd
  have hc : Measurable (fun p : E × E => if ‖(2 / ((L : ℝ) * (L + 1))) • p.2 - p.1‖ ≤
      ε / (4 * ρ) then p.1 else (2 / ((L : ℝ) * (L + 1))) • p.2) :=
    measurable_fst.ite (measurableSet_le (hy.sub measurable_fst).norm measurable_const) hy
  exact hc.prodMk (hc.prodMk measurable_const)

theorem step_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ G ε : ℝ) (L k : ℕ) :
    Measurable (fun p : State E × OracleReply E => step ρ G ε L k p.1 p.2) := by
  let j := k % L + 1
  have hx : Measurable (fun p : State E × OracleReply E => p.1.1) := measurable_fst.fst
  have hz : Measurable (fun p : State E × OracleReply E => p.1.2.1) := measurable_fst.snd.fst
  have hs : Measurable (fun p : State E × OracleReply E => p.1.2.2) := measurable_fst.snd.snd
  have ht : Measurable (fun p : State E × OracleReply E => p.1.2.2 + (j : ℝ) • p.1.2.1) :=
    hs.add (measurable_const.smul hz)
  have hv := minimumNormReply_measurable.comp (measurable_snd : Measurable (fun p : State E × OracleReply E => p.2))
  by_cases hj : k % L + 1 = L
  · simp only [step, hj, ↓reduceIte]
    simpa only [j, hj, Function.comp_def] using (finish_measurable ρ ε L).comp (hx.prodMk ht)
  · simp only [step, hj, ↓reduceIte]
    have harg : Measurable (fun p : State E × OracleReply E => p.1.2.1 -
        (2 / (ρ * ((j : ℝ) + 1))) • (minimumNormReply p.2 + (2 * ρ) • (p.1.2.1 - p.1.1))) :=
      hz.sub (measurable_const.smul (hv.add (measurable_const.smul (hz.sub hx))))
    have hn := (ballProject_measurable_joint (G / ρ)).comp (hx.prodMk harg)
    exact hx.prodMk (hn.prodMk ht)

theorem replay_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ G ε : ℝ) (L t : ℕ) : Measurable (replay (E := E) ρ G ε L t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp : Measurable (fun replies : Fin (t + 1) → OracleReply E =>
        fun j : Fin t => replies j.castSucc) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply j.castSucc
    exact (step_measurable ρ G ε L t).comp
      ((ih.comp hp).prodMk (measurable_pi_apply (Fin.last t)))

def algorithm (ρ G ε : ℝ) (L : ℕ) : Model.BorelAlgorithm where
  decision d t := fun p => (replay (E := Model.Space d) ρ G ε L t p.2).2.1
  measurable_decision d t := by
    have hm := ((replay_measurable (E := Model.Space d) ρ G ε L t).comp
      (measurable_snd : Measurable (fun p : ℝ × (Fin t → Model.Reply d) => p.2))).snd.fst
    have hsrc : (inferInstance : MeasurableSpace (ℝ × (Fin t → Model.Reply d))) =
        borel (ℝ × (Fin t → Model.Reply d)) := BorelSpace.measurable_eq
    exact hm.mono hsrc.le le_rfl

def execution [ProperSpace E] [CompleteSpace E] {ρ G : ℝ} {f : E → ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (ε : ℝ) (L : ℕ) : ℕ → State E
  | 0 => (0, 0, 0)
  | k + 1 => let s := execution hG hρ hlip hwc ε L k
      step ρ G ε L k s (fullOracle hG hρ hlip hwc s.2.1)

theorem execution_coupling {ρ G Δ ε : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (I : Model.Instance G ρ Δ) (L : ℕ) (seed : ℝ) (t : ℕ) :
    (replay ρ G ε L t (fun j : Fin t => fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
      (Model.trajectory hG hρ (algorithm ρ G ε L) I seed j.val)) =
        execution hG hρ I.admissible.lipschitz I.admissible.weaklyConvex ε L t) ∧
    Model.trajectory hG hρ (algorithm ρ G ε L) I seed t =
      (execution hG hρ I.admissible.lipschitz I.admissible.weaklyConvex ε L t).2.1 := by
  induction t with
  | zero =>
    constructor
    · rfl
    · rw [Model.trajectory]; rfl
  | succ t ih =>
    have hreplay : replay ρ G ε L (t + 1) (fun j : Fin (t + 1) =>
        fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
          (Model.trajectory hG hρ (algorithm ρ G ε L) I seed j.val)) =
        execution hG hρ I.admissible.lipschitz I.admissible.weaklyConvex ε L (t + 1) := by
      rw [replay, execution]
      change step ρ G ε L t
        (replay ρ G ε L t (fun j : Fin t => fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
          (Model.trajectory hG hρ (algorithm ρ G ε L) I seed j.val)))
        (fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
          (Model.trajectory hG hρ (algorithm ρ G ε L) I seed t)) = _
      rw [ih.1, ih.2]
    refine ⟨hreplay, ?_⟩
    rw [Model.trajectory]
    exact congrArg (fun s : State (Model.Space I.dimension) => s.2.1) hreplay

theorem finish_inner_sum (ρ G ε : ℝ) (L : ℕ) (x : E) (select : E → E) :
    finish ρ ε L x (∑ k ∈ Finset.range L, ((k : ℝ) + 1) • proximalInnerIterate x ρ G select k) =
      (proximalOuterUpdate ρ G ε select L x, proximalOuterUpdate ρ G ε select L x, 0) := by
  simp only [finish, proximalOuterUpdate, proximalInnerAverage_formula]

theorem execution_round_prefix [ProperSpace E] [CompleteSpace E]
    {ρ G : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (ε : ℝ) (L r : ℕ) (x : E)
    (hstart : execution hG hρ hlip hwc ε L (r * L) = (x, x, 0))
    (n : ℕ) (hn : n < L) :
    let select := minimumNormSubgradient hG hρ hlip hwc
    execution hG hρ hlip hwc ε L (r * L + n) =
      (x, proximalInnerIterate x ρ G select n,
        ∑ k ∈ Finset.range n, ((k : ℝ) + 1) • proximalInnerIterate x ρ G select k) := by
  dsimp only
  induction n with
  | zero => simpa only [Nat.add_zero, proximalInnerIterate, Finset.sum_range_zero] using hstart
  | succ n ih =>
    have hprev := ih (by omega)
    rw [Nat.add_succ, execution, hprev]
    have hmod : (r * L + n) % L = n := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : n < L)]
    simp only [step, hmod, show ¬n + 1 = L by omega, ↓reduceIte]
    rw [Finset.sum_range_succ]
    have hden : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    rw [hden]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl

theorem execution_finish_round [ProperSpace E] [CompleteSpace E]
    {ρ G : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (ε : ℝ) {L : ℕ} (hL : 0 < L) (r : ℕ) (x : E)
    (hstart : execution hG hρ hlip hwc ε L (r * L) = (x, x, 0)) :
    let select := minimumNormSubgradient hG hρ hlip hwc
    execution hG hρ hlip hwc ε L (r * L + L) =
      (proximalOuterUpdate ρ G ε select L x, proximalOuterUpdate ρ G ε select L x, 0) := by
  dsimp only
  cases L with
  | zero => omega
  | succ n =>
    have hprefix := execution_round_prefix hG hρ hlip hwc ε (n + 1) r x hstart n (by omega)
    rw [show r * (n + 1) + (n + 1) = (r * (n + 1) + n) + 1 by omega, execution, hprefix]
    have hmod : (r * (n + 1) + n) % (n + 1) = n := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : n < n + 1)]
    simp only [step, hmod, ↓reduceIte]
    have hfinish := finish_inner_sum ρ G ε (n + 1) x (minimumNormSubgradient hG hρ hlip hwc)
    rw [Finset.sum_range_succ] at hfinish
    simpa only [Nat.cast_add, Nat.cast_one] using hfinish

theorem execution_outer_boundary [ProperSpace E] [CompleteSpace E]
    {ρ G : ℝ} {f : E → ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f)
    (ε : ℝ) {L : ℕ} (hL : 0 < L) (r : ℕ) :
    let select := minimumNormSubgradient hG hρ hlip hwc
    let x := proximalOuterIterate ρ G ε select L 0 r
    execution hG hρ hlip hwc ε L (r * L) = (x, x, 0) := by
  dsimp only
  induction r with
  | zero => simp only [Nat.zero_mul, execution, proximalOuterIterate]
  | succ r ih =>
    have hfinish := execution_finish_round hG hρ hlip hwc ε hL r
      (proximalOuterIterate ρ G ε (minimumNormSubgradient hG hρ hlip hwc) L 0 r) ih
    simpa only [Nat.succ_mul, proximalOuterIterate] using hfinish

theorem trajectory_outer_boundary {ρ G Δ ε : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (I : Model.Instance G ρ Δ) {L : ℕ} (hL : 0 < L) (seed : ℝ) (r : ℕ) :
    Model.trajectory hG hρ (algorithm ρ G ε L) I seed (r * L) =
      proximalOuterIterate ρ G ε (minimumNormSubgradient hG hρ I.admissible.lipschitz
        I.admissible.weaklyConvex) L 0 r := by
  have hcouple := (execution_coupling hG hρ I L seed (r * L) (ε := ε)).2
  rw [execution_outer_boundary hG hρ I.admissible.lipschitz I.admissible.weaklyConvex ε hL r] at hcouple
  exact hcouple

theorem algorithm_stationary_at_deadline {ρ G Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε)
    (I : Model.Instance G ρ Δ) (seed : ℝ) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (Model.trajectory hG.le hρ.le (algorithm ρ G ε (innerCallCount G ε)) I seed
        (outerRoundCount ρ Δ ε * innerCallCount G ε))‖ ≤ ε := by
  rw [trajectory_outer_boundary hG.le hρ.le I (innerCallCount_pos hG hε) seed]
  exact proximalOuterIterate_stationary
    (minimumNormSubgradient hG.le hρ.le I.admissible.lipschitz I.admissible.weaklyConvex)
    hρ hG.le hε I.admissible.lipschitz I.admissible.weaklyConvex I.admissible.gap
    (minimumNormSubgradient_mem hG.le hρ.le I.admissible.lipschitz I.admissible.weaklyConvex)
    (innerCallCount_pos hG hε) (innerCallCount_budget hε)
    (Nat.succ_pos _) (outerRoundCount_budget hρ hε)

theorem algorithm_successProbability_deadline {ρ G Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (I : Model.Instance G ρ Δ) :
    Model.successProbability hG.le hρ.le (algorithm ρ G ε (innerCallCount G ε)) I ε
      (outerRoundCount ρ Δ ε * innerCallCount G ε) = 1 := by
  unfold Model.successProbability
  have heq : {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
      (Model.trajectory hG.le hρ.le (algorithm ρ G ε (innerCallCount G ε)) I seed
        (outerRoundCount ρ Δ ε * innerCallCount G ε))‖ ≤ ε} = Set.univ := by
    ext seed
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact algorithm_stationary_at_deadline hG hρ hε I seed
  rw [heq]
  exact MeasureTheory.measure_univ

theorem algorithm_hittingTime_le {ρ G Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hν : 0 ≤ ν) (I : Model.Instance G ρ Δ) :
    Model.hittingTime hG.le hρ.le (algorithm ρ G ε (innerCallCount G ε)) I ε ν ≤
      (outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) := by
  have hprob : ENNReal.ofReal (1 - ν) ≤ Model.successProbability hG.le hρ.le
      (algorithm ρ G ε (innerCallCount G ε)) I ε (outerRoundCount ρ Δ ε * innerCallCount G ε) := by
    rw [algorithm_successProbability_deadline hG hρ hε I]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  exact iInf_le_of_le ⟨outerRoundCount ρ Δ ε * innerCallCount G ε, hprob⟩ le_rfl

theorem actual_call_count {ρ G Δ ε : ℝ} (hε : 0 < ε)
    (hGε : ε ^ 2 ≤ G ^ 2) (hΔε : ε ^ 2 ≤ ρ * Δ) :
    ((outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) : ℝ) ≤
      540705 * ρ * G ^ 2 * Δ / ε ^ 4 := by
  have hb : 1 ≤ G ^ 2 / ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa using hGε)
  have hs : 1 ≤ ρ * Δ / ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa using hΔε)
  have hcount := upper_call_count hb hs
  have hcount' : (innerCallCount G ε : ℝ) * (outerRoundCount ρ Δ ε : ℝ) ≤
      540705 * (G ^ 2 / ε ^ 2) * (ρ * Δ / ε ^ 2) := by
    simpa only [innerCallCount, outerRoundCount, Nat.cast_add, Nat.cast_one] using hcount
  calc
    ((outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) : ℝ) =
        (innerCallCount G ε : ℝ) * (outerRoundCount ρ Δ ε : ℝ) := by push_cast; ring
    _ ≤ 540705 * (G ^ 2 / ε ^ 2) * (ρ * Δ / ε ^ 2) := hcount'
    _ = _ := by field_simp

/-- A complete deterministic upper bound in the manuscript's actual oracle-complexity model. -/
theorem oracleComplexity_upper {ρ G Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hν : 0 ≤ ν)
    (hGε : ε ^ 2 ≤ G ^ 2) (hΔε : ε ^ 2 ≤ ρ * Δ) :
    Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le ≤
      ENNReal.ofReal (540705 * ρ * G ^ 2 * Δ / ε ^ 4) := by
  have hdeadline : Model.oracleComplexity G ρ Δ ε ν hG.le hρ.le ≤
      ((outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) : ℝ≥0∞) := by
    apply iInf_le_of_le (algorithm ρ G ε (innerCallCount G ε))
    apply iSup_le
    intro I
    exact algorithm_hittingTime_le hG hρ hε hν I
  have hnat : ((outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((outerRoundCount ρ Δ ε * innerCallCount G ε : ℕ) : ℝ) := by simp
  rw [hnat] at hdeadline
  exact hdeadline.trans (ENNReal.ofReal_le_ofReal (actual_call_count hε hGε hΔε))

end UpperModel
end WC
