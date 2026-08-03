import WeaklyConvexLowerBound.BatchResisting
import WeaklyConvexLowerBound.RotationInvariance
import WeaklyConvexLowerBound.ScaledZeroRespecting
import WeaklyConvexLowerBound.MoreauSemantics

/-!
# Deterministic full-oracle lower-bound assembly

This file combines the batch resisting construction with the concrete scaled
hard value.  The oracle reply always contains the entire semantic full
subdifferential.  The ambient stationarity field is the selected proximal
residual

`‖2ρ (X - prox_{f/(2ρ)} X)‖₂`.

For the canonical selector below, `MoreauSemantics` identifies the normalized
residual with the genuine gradient of the half Moreau envelope; the exact
paper scaling and orthogonal rotation transport that identity to the ambient
problem.  Thus the selector-based field is an executable presentation of the
paper's true Moreau-gradient norm, rather than a surrogate oracle quantity.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-! ## Complete flattened base replies -/

/-- Serialize a block objective and its *entire* semantic full
subdifferential into the dimension-correct base oracle model. -/
def flattenedFullOracleReply {M N : Nat} (ρ : ℝ)
    (f : BlockVec M N → ℝ) (x : EVector (M * N)) :
    FullOracleReply (M * N) where
  value := f (unflatten x)
  subdiff := flatten '' fullSubdiff ρ f (unflatten x)

@[simp] theorem flattenedFullOracleReply_value {M N : Nat} (ρ : ℝ)
    (f : BlockVec M N → ℝ) (x : EVector (M * N)) :
    (flattenedFullOracleReply ρ f x).value = f (unflatten x) := rfl

@[simp] theorem flattenedFullOracleReply_subdiff {M N : Nat} (ρ : ℝ)
    (f : BlockVec M N → ℝ) (x : EVector (M * N)) :
    (flattenedFullOracleReply ρ f x).subdiff =
      flatten '' fullSubdiff ρ f (unflatten x) := rfl

theorem flattenedFullOracleReply_at_flatten {M N : Nat} (ρ : ℝ)
    (f : BlockVec M N → ℝ) (z : BlockVec M N) :
    (flattenedFullOracleReply ρ f (flatten z)).subdiff =
      flatten '' fullSubdiff ρ f z := by
  simp

/-! ## The ambient rotated problem -/

/-- Stationarity is read from the base selected proximal residual after
orthogonal projection.  Rotation covariance of proximal minimizers makes
this exactly the ambient Moreau-gradient norm. -/
def rotatedSelectedStationarity {M N D : Nat}
    (U : Fin (M * N) → EVector D)
    (baseStationarity : BlockVec M N → ℝ) (X : EVector D) : ℝ :=
  baseStationarity (blockProject U X)

/-- Ambient proximal minimizer for quadratic coefficient `ρ`. -/
def EVectorIsRhoProxPoint {D : Nat} (ρ : ℝ) (f : EVector D → ℝ)
    (X Z : EVector D) : Prop :=
  ∀ Y, f Z + ρ * WeaklyConvexLowerBound.Foundation.vecSq (Z - X) ≤
    f Y + ρ * WeaklyConvexLowerBound.Foundation.vecSq (Y - X)

/-- Ambient Moreau-gradient residual at envelope parameter `1/(2ρ)`. -/
def eVectorRhoResidual {D : Nat} (ρ : ℝ)
    (X Z : EVector D) : EVector D :=
  (2 * ρ) • (X - Z)

theorem IsRhoProxPoint.rotate {M N D : Nat} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {f : BlockVec M N → ℝ} {X : EVector D} {z : BlockVec M N}
    (hz : IsRhoProxPoint ρ f (blockProject U X) z) :
    EVectorIsRhoProxPoint ρ (rotatedValue f U) X
      (ambientProxLift U X z) := by
  intro Y
  have hbase := hz (blockProject U Y)
  have hcontract :
      blockSq (blockProject U Y - blockProject U X) ≤
        WeaklyConvexLowerBound.Foundation.vecSq (Y - X) := by
    rw [← blockProject_sub]
    exact blockSq_blockProject_le hU _
  have hscaled := mul_le_mul_of_nonneg_left hcontract hρ
  unfold rotatedValue
  rw [blockProject_ambientProxLift hU,
    vecSq_ambientProxLift_sub hU]
  nlinarith

theorem eVectorRhoResidual_ambientProxLift {M N D : Nat}
    (ρ : ℝ) (U : Fin (M * N) → EVector D)
    (X : EVector D) (z : BlockVec M N) :
    eVectorRhoResidual ρ X (ambientProxLift U X z) =
      blockEmbed U (rhoResidual ρ (blockProject U X) z) := by
  have hsub : X - ambientProxLift U X z =
      blockEmbed U (blockProject U X - z) := by
    unfold ambientProxLift
    calc
      X - (X + blockEmbed U (z - blockProject U X)) =
          -blockEmbed U (z - blockProject U X) := by module
      _ = blockEmbed U (-(z - blockProject U X)) := by
        rw [show -blockEmbed U (z - blockProject U X) =
          (-1 : ℝ) • blockEmbed U (z - blockProject U X) by simp,
          ← blockEmbed_smul]
        congr 1
        simp
      _ = blockEmbed U (blockProject U X - z) := by
        congr 1
        module
  unfold eVectorRhoResidual rhoResidual
  rw [hsub, ← blockEmbed_smul]

theorem vecSq_eVectorRhoResidual_ambientProxLift {M N D : Nat}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    (ρ : ℝ) (X : EVector D) (z : BlockVec M N) :
    WeaklyConvexLowerBound.Foundation.vecSq
        (eVectorRhoResidual ρ X (ambientProxLift U X z)) =
      blockSq (rhoResidual ρ (blockProject U X) z) := by
  rw [eVectorRhoResidual_ambientProxLift,
    blockSq_blockEmbed hU]

/-- The projected stationarity field is literally the norm of a selected
ambient `ρ`-proximal residual. -/
theorem rotatedSelectedStationarity_eq_ambientResidual
    {M N D : Nat} {ρ : ℝ}
    {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {f : BlockVec M N → ℝ} (P : RhoProxSelector ρ f)
    (X : EVector D) :
    rotatedSelectedStationarity U P.stationarity X =
      Real.sqrt (WeaklyConvexLowerBound.Foundation.vecSq
        (eVectorRhoResidual ρ X
          (ambientProxLift U X (P.prox (blockProject U X))))) := by
  unfold rotatedSelectedStationarity RhoProxSelector.stationarity
  rw [vecSq_eVectorRhoResidual_ambientProxLift hU]

theorem rotatedSelectedProx_isProx {M N D : Nat} {ρ : ℝ}
    (hρ : 0 ≤ ρ) {U : Fin (M * N) → EVector D}
    (hU : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U)
    {f : BlockVec M N → ℝ} (P : RhoProxSelector ρ f)
    (X : EVector D) :
    EVectorIsRhoProxPoint ρ (rotatedValue f U) X
      (ambientProxLift U X (P.prox (blockProject U X))) :=
  (P.isProx (blockProject U X)).rotate hρ hU

/-- A dimension-correct ambient problem with exact value/full-set oracle and
the selected Moreau stationarity field. -/
def rotatedFullOracleProblem {M N D : Nat} (ρ : ℝ)
    (f : BlockVec M N → ℝ) (U : Fin (M * N) → EVector D)
    (baseStationarity : BlockVec M N → ℝ) : FullOracleProblem D where
  objective := rotatedValue f U
  subdiff := eVectorFullSubdiff ρ (rotatedValue f U)
  stationarity := rotatedSelectedStationarity U baseStationarity

theorem PublishedFrame.embed_flatten {M N T : Nat}
    (F : PublishedFrame (M * N) T) (g : BlockVec M N) :
    F.embed (flatten g) = blockEmbed F.column g := by
  rfl

/-- Exact equality of the concrete ambient full oracle with the synthetic
reply used by the batch construction.  The subdifferential field is proved
with `eVectorFullSubdiff_rotate_eq`; both set inclusions are therefore
present, rather than assumed. -/
theorem fullOracle_rotated_eq_rotateBaseReply {M N T : Nat}
    (ρ : ℝ) (hρ : 0 ≤ ρ) (f : BlockVec M N → ℝ)
    (F : PublishedFrame (M * N) T)
    (hF : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame F.column)
    (baseStationarity : BlockVec M N → ℝ) (X : EVector (M * N + T)) :
    fullOracle (rotatedFullOracleProblem ρ f F.column baseStationarity) X =
      rotateBaseReply F
        (flattenedFullOracleReply ρ f (F.project X)) := by
  unfold fullOracle rotatedFullOracleProblem rotateBaseReply
    flattenedFullOracleReply
  congr 1
  change eVectorFullSubdiff ρ (rotatedValue f F.column) X =
    F.embed '' (flatten '' fullSubdiff ρ f (unflatten (F.project X)))
  rw [eVectorFullSubdiff_rotate_eq hF hρ]
  ext G
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨flatten g, ?_, ?_⟩
    · exact ⟨g, hg, rfl⟩
    · rfl
  · rintro ⟨gflat, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

/-! ## Canonical paper stationarity -/

/-- Canonical normalized proximal selector supplied by
`MoreauSemantics`. -/
def canonicalHardValueSelector {M N : Nat} (hA : Admissible M N) :
    HalfProxSelector (hardValue : BlockVec M N → ℝ) where
  prox := halfProxMap (hardValueHalfProxExistence hA)
  isProx := halfProxMap_spec (hardValueHalfProxExistence hA)

/-- Its selected residual is the genuine half-Moreau gradient norm squared.
This theorem is the formal semantic connection used by the assembly. -/
theorem canonicalHardValueSelector_stationarity_sq {M N : Nat}
    (hA : Admissible M N) (x : BlockVec M N) :
    (canonicalHardValueSelector hA).stationarity x ^ 2 =
      blockEuclideanNorm
        (halfMoreauGradient (hardValueHalfProxExistence hA) x) ^ 2 := by
  unfold HalfProxSelector.stationarity canonicalHardValueSelector
  rw [Real.sq_sqrt]
  · symm
    exact hardValue_halfMoreauGradient_euclidean_norm_sq hA x
  · exact blockSq_nonneg _

/-! ## Paper parameters and the concrete hard subclass -/

abbrev paperM (G ρ Δ ε : ℝ) : Nat := parameterM G ρ Δ ε
abbrev paperN (G ε : ℝ) : Nat := parameterN G ε
abbrev paperH (G ρ Δ ε : ℝ) : Nat :=
  horizon (paperM G ρ Δ ε) (paperN G ε)

/-- Query count, not final query index.  Thus `paperT = paperH + 1` and
`t < paperT` is definitionally the same finite range as `t ≤ paperH`. -/
abbrev paperT (G ρ Δ ε : ℝ) : Nat := paperH G ρ Δ ε + 1

abbrev paperBaseDim (G ρ Δ ε : ℝ) : Nat :=
  paperM G ρ Δ ε * paperN G ε

abbrev paperAmbientDim (G ρ Δ ε : ℝ) : Nat :=
  paperBaseDim G ρ Δ ε + paperT G ρ Δ ε

def paperScaledHardValue (G ρ Δ ε : ℝ) :
    BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ :=
  scaledFunction (G ^ 2 / ρ) (ρ / G) hardValue

def paperFlattenedBaseReply (G ρ Δ ε : ℝ) :
    EVector (paperBaseDim G ρ Δ ε) →
      FullOracleReply (paperBaseDim G ρ Δ ε) :=
  flattenedFullOracleReply ρ (paperScaledHardValue G ρ Δ ε)

def paperCanonicalHalfSelector {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    HalfProxSelector
      (hardValue : BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ) :=
  canonicalHardValueSelector
    (parameters_admissible hG hρ hΔ hε hacc)

def paperCanonicalRhoSelector {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    RhoProxSelector ρ (paperScaledHardValue G ρ Δ ε) :=
  (paperCanonicalHalfSelector hG hρ hΔ hε hacc).paperScaled hG hρ

/-- A concrete hard subclass of the paper's ambient problem class.  The
stationarity field is fixed to the canonical selected Moreau residual. -/
def SelectedScaledHardProblemClass {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    DimensionedProblemClass :=
  fun D P => ∃ U : Fin (paperBaseDim G ρ Δ ε) → EVector D,
    WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame U ∧
    P = rotatedFullOracleProblem ρ (paperScaledHardValue G ρ Δ ε) U
      (paperCanonicalRhoSelector hG hρ hΔ hε hacc).stationarity

/-! ## One arbitrary deterministic component -/

/-- Every deterministic component in dimension `d+T` has a concrete rotated
scaled-hard problem on which all first `T=H+1` queries fail.  Equivalently,
the failed query indices are exactly `0,…,H`, including the terminal index
covered by `scaled_zeroRespecting_failure_through_horizon`. -/
theorem deterministicComponent_scaledHard_failure
    {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ) z →
        HardFormulaReply z g)
    (A : DeterministicFullOracleComponent (paperAmbientDim G ρ Δ ε)) :
    ∃ P : FullOracleProblem (paperAmbientDim G ρ Δ ε),
      SelectedScaledHardProblemClass hG hρ hΔ hε hacc
        (paperAmbientDim G ρ Δ ε) P ∧
      DeterministicFullOracleComponent.FailsWithin A P ε
        (paperT G ρ Δ ε) := by
  let baseOracle := paperFlattenedBaseReply G ρ Δ ε
  let C := Classical.choice
    (exists_completedDynamicBatchTable
      (paperBaseDim G ρ Δ ε) (paperT G ρ Δ ε) A baseOracle)
  let selector := paperCanonicalRhoSelector hG hρ hΔ hε hacc
  let P : FullOracleProblem (paperAmbientDim G ρ Δ ε) :=
    rotatedFullOracleProblem ρ (paperScaledHardValue G ρ Δ ε)
      C.finalFrame.column selector.stationarity
  have hframe : WeaklyConvexLowerBound.Foundation.IsOrthonormalFrame C.finalFrame.column :=
    C.frame_orthonormal
  have hbaseSet : ∀ z,
      (baseOracle (flatten z)).subdiff =
        flatten '' fullSubdiff ρ (paperScaledHardValue G ρ Δ ε) z := by
    intro z
    exact flattenedFullOracleReply_at_flatten ρ
      (paperScaledHardValue G ρ Δ ε) z
  have hrotated : ∀ t,
      fullOracle P (C.adaptive.query t) =
        rotateBaseReply C.finalFrame
          (baseOracle (C.finalFrame.project (C.adaptive.query t))) := by
    intro t
    exact fullOracle_rotated_eq_rotateBaseReply ρ hρ.le
      (paperScaledHardValue G ρ Δ ε) C.finalFrame hframe
      selector.stationarity (C.adaptive.query t)
  obtain ⟨_htranscript, hactual, hzero, hproject⟩ :=
    C.actual_transcript_and_fullSetZeroRespecting
      (fullSubdiff ρ (paperScaledHardValue G ρ Δ ε)) P hbaseSet hrotated
  have hthrough := scaled_zeroRespecting_failure_through_horizon
    hG hρ hΔ hε hacc (paperCanonicalHalfSelector hG hρ hΔ hε hacc)
      hgeneral hpositive hzero
  refine ⟨P, ?_, ?_⟩
  · refine ⟨C.finalFrame.column, hframe, rfl⟩
  · intro t ht hhit
    have htH : t ≤ paperH G ρ Δ ε := by
      change t < paperH G ρ Δ ε + 1 at ht
      omega
    have hbaseFail := hthrough t htH
    let ti : Fin (paperT G ρ Δ ε) := ⟨t, ht⟩
    have hproj := hproject ti
    have hproj' : blockProject C.finalFrame.column
        (DeterministicFullOracleComponent.queriedAt A P t) = C.blockQuery t := by
      exact hproj.symm
    change selector.stationarity
      (blockProject C.finalFrame.column
        (DeterministicFullOracleComponent.queriedAt A P t)) ≤ ε at hhit
    rw [hproj'] at hhit
    exact (not_lt_of_ge hhit) hbaseFail

/-! ## Dimension-wise deterministic complexity -/

/-- The selected scaled-hard subclass has deterministic full-oracle
complexity at least `paperT`.  Since `paperT=paperH+1`, this records failure
at the terminal query itself and removes the manuscript's off-by-one
ambiguity. -/
theorem selectedScaledHard_fullOracleComplexityAtLeast
    {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ))
    (hgeneral : ∀ z g,
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ) z →
        GeneralHardFormulaReply z g)
    (hpositive : ∀ z g, 0 < activationNorm z →
      g ∈ fullSubdiff 1
          (hardValue : BlockVec (paperM G ρ Δ ε) (paperN G ε) → ℝ) z →
        HardFormulaReply z g) :
    FullOracleComplexityAtLeast
      (SelectedScaledHardProblemClass hG hρ hΔ hε hacc) ε
      (paperT G ρ Δ ε) := by
  intro Alg
  obtain ⟨P, hmem, hfail⟩ := deterministicComponent_scaledHard_failure
    hG hρ hΔ hε hacc hgeneral hpositive
      (Alg.component (paperAmbientDim G ρ Δ ε))
  exact ⟨paperAmbientDim G ρ Δ ε, P, hmem, hfail⟩

/-- The query-count lower bound also has the advertised numerical scale. -/
theorem paperT_rate_lower
    {G ρ Δ ε : ℝ}
    (hG : 0 < G) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hacc : ε ^ 2 ≤ paperC0 * min (G ^ 2) (ρ * Δ)) :
    paperC1 * (G ^ 2 * min (ρ * Δ) (G ^ 2) / ε ^ 4) ≤
      (paperT G ρ Δ ε : ℝ) := by
  have hH := selected_horizon_rate_lower hG hρ hΔ hε hacc
  exact hH.trans (by norm_num [paperT])

end

end WeaklyConvexLowerBound

