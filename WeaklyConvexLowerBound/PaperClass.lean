import WeaklyConvexLowerBound.DeterministicAssembly
import WeaklyConvexLowerBound.AmbientMoreauSemantics
import WeaklyConvexLowerBound.Gap

/-!
# The dimension-correct manuscript problem class

This file closes the class-membership side of the deterministic reduction.
The class below records the literal ambient objective, its complete semantic
full subdifferential, and the norm of the genuine Frechet derivative of the
ambient Moreau envelope.  In particular, the stationarity field is not an
uninterpreted surrogate.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set

/-- The stationarity field of an ambient problem is the Euclidean norm of a
vector representing the Frechet derivative of its literal `rho`-Moreau
envelope at every point. -/
def HasLiteralAmbientMoreauStationarity {D : Nat} (rho : ℝ)
    (P : FullOracleProblem D) : Prop :=
  ∃ grad : EVector D → EVector D,
    (∀ X, HasFDerivAt (eVectorRhoMoreauEnvelope rho P.objective)
      (eVectorGradientCLM (grad X)) X) ∧
    ∀ X, P.stationarity X = eVectorEuclideanNorm (grad X)

/-- Dimension-indexed version of the manuscript class
`F(G, rho, Delta)`.  Boundedness below is recorded explicitly so that the
real-valued `sInf` expression in the initial-gap field has its intended
meaning. -/
def PaperProblemClass (G rho Delta : ℝ) : DimensionedProblemClass :=
  fun _ P =>
    EVectorWeaklyConvex rho P.objective ∧
    EVectorEuclideanLipschitz G P.objective ∧
    BddBelow (Set.range P.objective) ∧
    P.objective 0 - sInf (Set.range P.objective) ≤ Delta ∧
    P.subdiff = eVectorFullSubdiff rho P.objective ∧
    HasLiteralAmbientMoreauStationarity rho P

/-! ## Scaling preserves the order-theoretic class fields -/

theorem bddBelow_range_scaledFunction {M N : Nat}
    {amp scale : ℝ} (hamp : 0 ≤ amp) {f : BlockVec M N → ℝ}
    (hf : BddBelow (Set.range f)) :
    BddBelow (Set.range (scaledFunction amp scale f)) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨amp * b, ?_⟩
  rintro _ ⟨x, rfl⟩
  unfold scaledFunction
  exact mul_le_mul_of_nonneg_left
    (hb (Set.mem_range_self (scaleVec scale x))) hamp

theorem paperScaledHardValue_bddBelow
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    BddBelow (Set.range (paperScaledHardValue G rho Delta eps)) := by
  let hA := parameters_admissible hG hrho hDelta heps hacc
  unfold paperScaledHardValue
  exact bddBelow_range_scaledFunction (by positivity)
    (hardValue_range_bddBelow hA.N_pos)

/-- The literal scaled initial gap is at most `Delta`.  The proof retains
the clipped ratio used in the manuscript, rather than weakening the estimate
to the large-gap regime. -/
theorem paperScaledHardValue_initialGap_le
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    paperScaledHardValue G rho Delta eps 0 -
        sInf (Set.range (paperScaledHardValue G rho Delta eps)) ≤ Delta := by
  let M := paperM G rho Delta eps
  let N := paperN G eps
  let amp : ℝ := G ^ 2 / rho
  let scale : ℝ := rho / G
  let hA : Admissible M N :=
    parameters_admissible hG hrho hDelta heps hacc
  have hamp : 0 < amp := by
    dsimp [amp]
    positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hA.N_pos
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hA.M_ge
  have hlower : ∀ x : BlockVec M N,
      amp * (-(2 * (M : ℝ) / (N : ℝ))) ≤
        paperScaledHardValue G rho Delta eps x := by
    intro x
    change amp * (-(2 * (M : ℝ) / (N : ℝ))) ≤
      amp * hardValue (scaleVec scale x)
    exact mul_le_mul_of_nonneg_left
      (hardValue_lower hA.N_pos (scaleVec scale x)) hamp.le
  have hinf : amp * (-(2 * (M : ℝ) / (N : ℝ))) ≤
      sInf (Set.range (paperScaledHardValue G rho Delta eps)) :=
    lower_bound_le_sInf_range _ _ hlower
  have hzeroBase := hardValue_zero_lt_two_div_N hA.M_ge hA.N_pos
  have hzero : paperScaledHardValue G rho Delta eps 0 ≤
      amp * (2 / (N : ℝ)) := by
    change amp * hardValue (scaleVec scale 0) ≤
      amp * (2 / (N : ℝ))
    have hz : scaleVec scale (0 : BlockVec M N) = 0 := by
      ext m j
      simp [scaleVec]
    rw [hz]
    exact (mul_lt_mul_of_pos_left hzeroBase hamp).le
  have hnumeric : 2 / (N : ℝ) + 2 * (M : ℝ) / (N : ℝ) ≤
      3 * (M : ℝ) / (N : ℝ) := by
    rw [← add_div, div_le_div_iff_of_pos_right hNreal]
    nlinarith
  have hgap : paperScaledHardValue G rho Delta eps 0 -
        sInf (Set.range (paperScaledHardValue G rho Delta eps)) ≤
      amp * (3 * (M : ℝ) / (N : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hnumeric hamp.le
    have hpre : paperScaledHardValue G rho Delta eps 0 -
          sInf (Set.range (paperScaledHardValue G rho Delta eps)) ≤
        amp * (2 / (N : ℝ) + 2 * (M : ℝ) / (N : ℝ)) := by
      nlinarith
    exact hpre.trans (by simpa [mul_add] using hmul)
  have hMraw : (M : ℝ) ≤
      (N : ℝ) * parameterR G rho Delta / 12 := by
    dsimp [M, N, paperM, paperN]
    unfold parameterM
    apply Nat.floor_le
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (parameterR_nonneg hG hrho hDelta)) (by norm_num)
  have hratio : 3 * (M : ℝ) / (N : ℝ) ≤
      parameterR G rho Delta / 4 := by
    rw [div_le_iff₀ hNreal]
    nlinarith
  have hproduct : G ^ 2 * parameterR G rho Delta ≤ rho * Delta := by
    rw [G_sq_mul_parameterR hG]
    exact min_le_left _ _
  have hampRatio : amp * parameterR G rho Delta ≤ Delta := by
    dsimp [amp]
    rw [show G ^ 2 / rho * parameterR G rho Delta =
      (G ^ 2 * parameterR G rho Delta) / rho by ring]
    calc
      (G ^ 2 * parameterR G rho Delta) / rho ≤
          (rho * Delta) / rho :=
        (div_le_div_iff_of_pos_right hrho).2 hproduct
      _ = Delta := by field_simp
  calc
    paperScaledHardValue G rho Delta eps 0 -
          sInf (Set.range (paperScaledHardValue G rho Delta eps)) ≤
        amp * (3 * (M : ℝ) / (N : ℝ)) := hgap
    _ ≤ amp * (parameterR G rho Delta / 4) :=
      mul_le_mul_of_nonneg_left hratio hamp.le
    _ = (amp * parameterR G rho Delta) / 4 := by ring
    _ ≤ Delta / 4 := div_le_div_of_nonneg_right hampRatio (by norm_num)
    _ ≤ Delta := by linarith

/-! ## The selected hard problems have literal Moreau stationarity -/

theorem paperSelectedStationarity_eq_actualGradientNorm
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta))
    {D : Nat} (U : Fin (paperBaseDim G rho Delta eps) → EVector D)
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U) (X : EVector D) :
    rotatedSelectedStationarity U
        (paperCanonicalRhoSelector hG hrho hDelta heps hacc).stationarity X =
      eVectorEuclideanNorm
        (ambientPaperScaledHardMoreauGradient U
          (G := G) (rho := rho)
          (parameters_admissible hG hrho hDelta heps hacc) X) := by
  let hA := parameters_admissible hG hrho hDelta heps hacc
  let d := halfProxResidual
    (scaleVec (rho / G) (blockProject U X))
    (halfProxMap (hardValueHalfProxExistence hA)
      (scaleVec (rho / G) (blockProject U X)))
  have hleft : rotatedSelectedStationarity U
        (paperCanonicalRhoSelector hG hrho hDelta heps hacc).stationarity X =
      G * Real.sqrt (blockSq d) := by
    have hs := paperScaled_stationarity hG hrho
      (paperCanonicalHalfSelector hG hrho hDelta heps hacc)
      (blockProject U X)
    simpa [rotatedSelectedStationarity, paperCanonicalRhoSelector,
      paperCanonicalHalfSelector, canonicalHardValueSelector,
      HalfProxSelector.stationarity, d, paperScaledHardValue] using hs
  have hleftSq :
      (rotatedSelectedStationarity U
        (paperCanonicalRhoSelector hG hrho hDelta heps hacc).stationarity X) ^ 2 =
        G ^ 2 * blockSq d := by
    rw [hleft, mul_pow, Real.sq_sqrt (blockSq_nonneg d)]
  have hrightSq := ambientPaperScaledHard_gradient_norm_sq
    hU hG hrho hA X
  change eVectorEuclideanNorm
      (ambientPaperScaledHardMoreauGradient U
        (G := G) (rho := rho) hA X) ^ 2 =
      G ^ 2 * blockSq d at hrightSq
  have hleftNonneg : 0 ≤ rotatedSelectedStationarity U
      (paperCanonicalRhoSelector hG hrho hDelta heps hacc).stationarity X := by
    unfold rotatedSelectedStationarity RhoProxSelector.stationarity
    exact Real.sqrt_nonneg _
  have hrightNonneg : 0 ≤ eVectorEuclideanNorm
      (ambientPaperScaledHardMoreauGradient U
        (G := G) (rho := rho) hA X) := by
    unfold eVectorEuclideanNorm
    exact Real.sqrt_nonneg _
  nlinarith

/-! ## Membership and complexity transport -/

/-- Every selected rotated scaled-hard problem used by the resisting oracle
belongs to the literal manuscript class. -/
theorem selectedScaledHardProblemClass_subset_paperProblemClass
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta)) :
    ∀ D P, SelectedScaledHardProblemClass hG hrho hDelta heps hacc D P →
      PaperProblemClass G rho Delta D P := by
  intro D P hP
  obtain ⟨U, hU, rfl⟩ := hP
  let hA := parameters_admissible hG hrho hDelta heps hacc
  let f := paperScaledHardValue G rho Delta eps
  have hbaseWeak : WeaklyConvex rho f := by
    dsimp [f, paperScaledHardValue]
    exact weaklyConvex_paper_scaled hG hrho
      (hardValue_one_weaklyConvex hA)
  have hbaseLip : EuclideanLipschitz G f := by
    dsimp [f, paperScaledHardValue]
    have h := euclideanLipschitz_scaled
      (amp := G ^ 2 / rho) (scale := rho / G)
      (hardValue_euclideanLipschitz hA)
    rw [(paper_scaling_coefficients hG.ne' hrho.ne').1] at h
    simpa using h
  refine ⟨weaklyConvex_rotate hU hrho.le hbaseWeak,
    euclideanLipschitz_rotate hU hbaseLip, ?_, ?_, rfl, ?_⟩
  · exact (bddBelow_range_rotatedValue_iff hU f).2
      (paperScaledHardValue_bddBelow hG hrho hDelta heps hacc)
  · change rotatedValue (paperScaledHardValue G rho Delta eps) U 0 -
        sInf (Set.range
          (rotatedValue (paperScaledHardValue G rho Delta eps) U)) ≤ Delta
    rw [initialGap_rotate hU]
    exact paperScaledHardValue_initialGap_le hG hrho hDelta heps hacc
  · refine ⟨ambientPaperScaledHardMoreauGradient U
        (G := G) (rho := rho) hA, ?_, ?_⟩
    · intro X
      exact hasFDerivAt_ambientPaperScaledHard_moreau
        hU hG hrho hA X
    · intro X
      exact paperSelectedStationarity_eq_actualGradientNorm
        hG hrho hDelta heps hacc U hU X

/-- Worst-case query lower bounds are monotone under enlargement of the
problem class. -/
theorem fullOracleComplexityAtLeast_mono
    {C K : DimensionedProblemClass} {eps : ℝ} {T : Nat}
    (hCK : ∀ D P, C D P → K D P)
    (hC : FullOracleComplexityAtLeast C eps T) :
    FullOracleComplexityAtLeast K eps T := by
  intro A
  obtain ⟨D, P, hP, hfail⟩ := hC A
  exact ⟨D, P, hCK D P hP, hfail⟩

/-- Deterministic lower bound for the genuine manuscript problem class.
Only the two explicit subdifferential-formula inputs remain as parameters;
the oracle, class-membership, Moreau, scaling, rotation, and resisting
bridges are all discharged. -/
theorem paperProblemClass_fullOracleComplexityAtLeast
    {G rho Delta eps : ℝ}
    (hG : 0 < G) (hrho : 0 < rho) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (hacc : eps ^ 2 ≤ paperC0 * min (G ^ 2) (rho * Delta))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G rho Delta eps) (paperN G eps) → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G rho Delta eps) (paperN G eps) → ℝ) z →
        HardFormulaReply z g) :
    FullOracleComplexityAtLeast (PaperProblemClass G rho Delta) eps
      (paperT G rho Delta eps) := by
  apply fullOracleComplexityAtLeast_mono
    (selectedScaledHardProblemClass_subset_paperProblemClass
      hG hrho hDelta heps hacc)
  exact selectedScaledHard_fullOracleComplexityAtLeast
    hG hrho hDelta heps hacc hgeneral hpositive

end

end WeaklyConvexLowerBound

