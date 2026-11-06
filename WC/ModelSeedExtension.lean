import WC.Model

/-! The total-real seed convention in `Model.BorelAlgorithm` is exactly
as general as the manuscript's Borel rules on the closed unit interval:
continuous clamping extends every such rule and preserves every run. -/

noncomputable section
namespace WC.Model
open scoped Classical

abbrev UnitSeed := Set.Icc (0 : ℝ) 1

def clampSeed (s : ℝ) : UnitSeed :=
  ⟨min (max s 0) 1, le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

theorem clampSeed_continuous : Continuous clampSeed := by
  apply Continuous.subtype_mk
  exact (continuous_id.max continuous_const).min continuous_const

@[simp] theorem clampSeed_unit (s : UnitSeed) : clampSeed s.val = s := by
  apply Subtype.ext
  change min (max s.val 0) 1 = s.val
  rw [max_eq_left s.property.1, min_eq_left s.property.2]

structure UnitBorelAlgorithm where
  decision (d t : ℕ) : UnitSeed × (Fin t → Reply d) → Space d
  measurable_decision (d t : ℕ) :
    @Measurable _ _ (borel _) (borel _) (decision d t)

def UnitBorelAlgorithm.extend (A : UnitBorelAlgorithm) : BorelAlgorithm where
  decision d t p := A.decision d t (clampSeed p.1, p.2)
  measurable_decision d t := by
    have hc : Continuous (fun p : ℝ × (Fin t → Reply d) => (clampSeed p.1, p.2)) :=
      (clampSeed_continuous.comp continuous_fst).prodMk continuous_snd
    exact (A.measurable_decision d t).comp hc.borel_measurable

def BorelAlgorithm.restrict (A : BorelAlgorithm) : UnitBorelAlgorithm where
  decision d t p := A.decision d t (p.1.val, p.2)
  measurable_decision d t := by
    have hc : Continuous (fun p : UnitSeed × (Fin t → Reply d) => (p.1.val, p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (A.measurable_decision d t).comp hc.borel_measurable

@[simp] theorem UnitBorelAlgorithm.extend_decision_unit (A : UnitBorelAlgorithm)
    (d t : ℕ) (s : UnitSeed) (transcript : Fin t → Reply d) :
    A.extend.decision d t (s.val, transcript) = A.decision d t (s, transcript) := by
  simp only [UnitBorelAlgorithm.extend, clampSeed_unit]

@[simp] theorem UnitBorelAlgorithm.restrict_extend_decision (A : UnitBorelAlgorithm)
    (d t : ℕ) (p : UnitSeed × (Fin t → Reply d)) :
    A.extend.restrict.decision d t p = A.decision d t p := by
  exact A.extend_decision_unit d t p.1 p.2

def UnitBorelAlgorithm.trajectory {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : UnitBorelAlgorithm) (I : Instance G ρ Δ) (seed : UnitSeed) (t : ℕ) : Space I.dimension :=
  match t with
  | 0 => 0
  | n + 1 => A.decision I.dimension (n + 1) (seed, fun s : Fin (n + 1) =>
      fullOracle hG hρ I.admissible.lipschitz I.admissible.weaklyConvex
        (A.trajectory hG hρ I seed s.val))
termination_by t
decreasing_by exact s.isLt

theorem UnitBorelAlgorithm.extend_trajectory {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : UnitBorelAlgorithm) (I : Instance G ρ Δ) (seed : UnitSeed) (t : ℕ) :
    Model.trajectory hG hρ A.extend I seed.val t = A.trajectory hG hρ I seed t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => rw [Model.trajectory, UnitBorelAlgorithm.trajectory]
    | succ n =>
      rw [Model.trajectory, UnitBorelAlgorithm.trajectory, A.extend_decision_unit]
      congr 1
      congr 1
      funext j
      rw [ih j j.isLt]

theorem BorelAlgorithm.restrict_trajectory {G ρ Δ : ℝ} (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (A : BorelAlgorithm) (I : Instance G ρ Δ) (seed : UnitSeed) (t : ℕ) :
    Model.trajectory hG hρ A I seed.val t = A.restrict.trajectory hG hρ I seed t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => rw [Model.trajectory, UnitBorelAlgorithm.trajectory]
    | succ n =>
      rw [Model.trajectory, UnitBorelAlgorithm.trajectory]
      change A.decision I.dimension (n + 1) (seed.val, _) = A.decision I.dimension (n + 1) (seed.val, _)
      congr 1
      congr 1
      funext j
      rw [ih j j.isLt]

end WC.Model
