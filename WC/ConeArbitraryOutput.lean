import WC.BoundaryLower

/-! A fixed cone defeats any Borel output produced without an oracle query.
The output can be unbounded and is evaluated without modifying it. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WC
namespace BoundaryLower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

theorem cone_stationary_geometry {G ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G) (u x : E) (hu : ‖u‖ = 1)
    (hstat : ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (normCone (coneVelocity G ε) (coneOffset ρ G ε • u))) x‖ ≤ ε) :
    ‖x‖ ≤ 2 * coneOffset ρ G ε ∧ coneOffset ρ G ε / 4 ≤ inner ℝ u x := by
  obtain ⟨hεv, _, _⟩ := coneVelocity_bounds hε hεG
  obtain ⟨_, ha, hratio⟩ := cone_certificate hρ hε hεG u hu
  have hrad := (div_le_iff₀ ha).mp hratio
  have hdist := (normCone_stationary_iff (hε.trans hεv) hρ hεv _ x).mp hstat
  have htriangle := norm_add_le (x - coneOffset ρ G ε • u) (coneOffset ρ G ε • u)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one] at htriangle
  have hinner := real_inner_le_norm u (coneOffset ρ G ε • u - x)
  rw [hu, one_mul, norm_sub_rev] at hinner
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  rw [inner_sub_right, real_inner_smul_right, huu, mul_one] at hinner
  constructor <;> nlinarith

end BoundaryLower

namespace ConeArbitraryOutput

open BoundaryLower Rotation.Normalized

theorem fixed_dimension {d : ℕ} [NeZero d] {G ρ ε δ : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hd : 2 ≤ d) (hbudget : 256 / (d : ℝ) ≤ δ)
    (z : ℝ → Model.Space d) (hz : Measurable z) :
    ∃ u : Model.Space d, ‖u‖ = 1 ∧
      Admissible G ρ (ε ^ 2 / ρ) (normCone (coneVelocity G ε) (coneOffset ρ G ε • u)) ∧
      Model.seedMeasure {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ))
        (normCone (coneVelocity G ε) (coneOffset ρ G ε • u))) (z seed)‖ ≤ ε} ≤ ENNReal.ofReal δ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let j : Fin d := ⟨0, by omega⟩
  let W : Unit → Submodule ℝ (Model.Space d) := fun _ => FrameGeometry.exposedSpan b ∅
  let v : ∀ i : Unit, (W i)ᗮ := fun _ => FrameGeometry.hiddenVector b ∅ j (by simp)
  have hn : ∀ i : Unit, Nontrivial (W i)ᗮ := fun _ =>
    FrameGeometry.complement_nontrivial b ∅ (K := 0) (by simp) hd
  have hu : ∀ i : Unit, ‖v i‖ = 1 := fun _ => FrameGeometry.hiddenVector_unit b ∅ j (by simp)
  let a := coneOffset ρ G ε
  have ha : 0 < a := (cone_certificate hρ hε hεG (b j) (b.orthonormal.norm_eq_one j)).2.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdim : ∀ i : Unit, (d : ℝ) ≤ (Module.finrank ℝ (W i)ᗮ : ℝ) := by
    intro i
    simpa only [Nat.cast_zero, sub_zero] using
      FrameGeometry.finrank_complement_ge_real b ∅ (K := 0) (by simp) (by omega)
  have hbudget' : (Fintype.card Unit : ℝ≥0∞) *
      ENNReal.ofReal (4 * (2 * a) ^ 2 / ((d : ℝ) * (a / 4) ^ 2)) ≤ ENNReal.ofReal δ := by
    have hid : 4 * (2 * a) ^ 2 / ((d : ℝ) * (a / 4) ^ 2) = 256 / (d : ℝ) := by
      field_simp
      ring
    simpa only [Fintype.card_unit, Nat.cast_one, one_mul, hid] using ENNReal.ofReal_le_ofReal hbudget
  obtain ⟨g, hg⟩ := Rotation.exists_fixed_frame_small_projections Model.seedMeasure W hn v hu
    (fun _ p => z p.2) (fun _ => hz.comp measurable_snd) (fun _ _ _ _ => rfl)
    (by positivity : 0 ≤ 2 * a) (by positivity : 0 < a / 4) hdR hdim (ENNReal.ofReal δ) hbudget'
  let u : Model.Space d := Frame.act (Model.Space d) g (v ())
  have hunit : ‖u‖ = 1 := (Frame.act (Model.Space d) g).norm_map (v ()) |>.trans (hu ())
  have hadm := (cone_certificate hρ hε hεG u hunit).1
  refine ⟨u, hunit, hadm, ?_⟩
  have hsuccess : MeasurableSet {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ))
      (normCone (coneVelocity G ε) (coneOffset ρ G ε • u))) (z seed)‖ ≤ ε} :=
    measurableSet_le (((moreau_gradient_continuous hG.le hρ hadm.lipschitz hadm.weaklyConvex).measurable.comp hz).norm)
      measurable_const
  have hlarge : ENNReal.ofReal (1 - δ) ≤ Model.seedMeasure {seed | ∀ i : Unit,
      ‖z seed‖ ≤ 2 * a → |inner ℝ (Frame.act (Model.Space d) g (v i : Model.Space d)) (z seed)| ≤ (a / 4) / 2} := by
    simpa [ENNReal.ofReal_sub 1 hδ.le] using hg
  apply LowerReduction.probability_le_of_disjoint_barrier Model.seedMeasure hsuccess hδ.le hδ_one hlarge
  intro seed hgood hstat
  have hgeom := cone_stationary_geometry hρ hε hεG u (z seed) hunit hstat
  have hinner := hgood () hgeom.1
  have habs := le_abs_self (inner ℝ u (z seed))
  change |inner ℝ u (z seed)| ≤ (a / 4) / 2 at hinner
  have hcoord : a / 4 ≤ inner ℝ u (z seed) := hgeom.2
  nlinarith

/-- A private-seed-dependent output with no queries cannot guarantee success:
one finite-dimensional admissible cone defeats it at the requested confidence. -/
theorem exists_hard_instance {G ρ Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (hgap : ε ^ 2 / ρ ≤ Δ) (hν : 0 ≤ ν) (hν_one : ν < 1)
    (z : ∀ d : ℕ, ℝ → Model.Space d) (hz : ∀ d, Measurable (z d)) :
    ∃ I : Model.Instance G ρ Δ,
      Model.seedMeasure {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
        (z I.dimension seed)‖ ≤ ε} < ENNReal.ofReal (1 - ν) := by
  let δ := (1 - ν) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_one : δ ≤ 1 := by dsimp [δ]; linarith
  let d := 2 + ⌈256 / δ⌉₊
  have hd : 2 ≤ d := by dsimp only [d]; omega
  letI : NeZero d := ⟨by omega⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hbudget : 256 / (d : ℝ) ≤ δ := by
    have hceil : 256 / δ ≤ (⌈256 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hdim : (⌈256 / δ⌉₊ : ℝ) ≤ d := by
      exact_mod_cast (show ⌈256 / δ⌉₊ ≤ d by dsimp only [d]; omega)
    have hm := (div_le_iff₀ hδ).mp (hceil.trans hdim)
    apply (div_le_iff₀ hdR).mpr
    nlinarith
  obtain ⟨u, hunit, hadm, hprob⟩ := fixed_dimension hG hρ hε hεG hδ hδ_one hd hbudget (z d) (hz d)
  let I : Model.Instance G ρ Δ :=
    ⟨d, normCone (coneVelocity G ε) (coneOffset ρ G ε • u),
      ⟨hadm.weaklyConvex, hadm.lipschitz, hadm.gap.mono hgap⟩⟩
  refine ⟨I, hprob.trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 1 - ν)).mpr
  dsimp [δ]
  linarith

theorem exists_hard_instance_for_output_rules {G ρ Δ ε ν : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hε : 0 < ε) (hεG : ε < G)
    (hgap : ε ^ 2 / ρ ≤ Δ) (hν : 0 ≤ ν) (hν_one : ν < 1)
    (output : ∀ d : ℕ, Model.BorelOutputRule d 0) :
    ∃ I : Model.Instance G ρ Δ,
      Model.seedMeasure {seed | ‖gradient (moreauEnvelope (1 / (2 * ρ)) I.objective)
        ((output I.dimension).output (seed, fun j => Fin.elim0 j))‖ ≤ ε} < ENNReal.ofReal (1 - ν) := by
  apply exists_hard_instance hG hρ hε hεG hgap hν hν_one
    (fun d seed => (output d).output (seed, fun j => Fin.elim0 j))
  intro d
  have hout := Rotation.Normalized.measurable_from_borel (output d).measurable_output
  exact hout.comp (measurable_id.prodMk measurable_const)

end ConeArbitraryOutput
end WC
