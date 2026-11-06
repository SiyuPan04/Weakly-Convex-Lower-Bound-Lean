import WC.Frame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Moments.Basic

/-! Exponential spherical concentration from orthogonal sign symmetrization.
This proof uses the actual invariant sphere measure and finite sign averaging;
it assumes neither a tail estimate nor a conditional distribution identity. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace MP.Concentration

def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signFlip (s : ι → Bool) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => sign (s i) * x i)
  invFun x := WithLp.toLp 2 (fun i => sign (s i) * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_assoc, mul_comm, mul_left_comm]
  left_inv x := by
    ext i
    change sign (s i) * (sign (s i) * x i) = x i
    cases h : s i <;> simp [h, sign]
  right_inv x := by
    ext i
    change sign (s i) * (sign (s i) * x i) = x i
    cases h : s i <;> simp [h, sign]
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun i => sign (s i) * x i)‖ = ‖x‖
    have heq : ‖WithLp.toLp 2 (fun i => sign (s i) * x i)‖ ^ 2 = ‖x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, mul_pow]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => sign (s i) * x i)), norm_nonneg x]

@[simp] theorem signFlip_apply (s : ι → Bool) (x : EuclideanSpace ℝ ι) (i : ι) :
    signFlip s x i = sign (s i) * x i := rfl

theorem sign_exp_sum (v : ι → ℝ) :
    (∑ s : ι → Bool, Real.exp (∑ i, sign (s i) * v i)) =
      (2 : ℝ) ^ Fintype.card ι * ∏ i, Real.cosh (v i) := by
  have h := Fintype.prod_sum (fun i (b : Bool) => Real.exp (sign b * v i))
  have hexp (s : ι → Bool) : Real.exp (∑ i, sign (s i) * v i) =
      ∏ i, Real.exp (sign (s i) * v i) := Real.exp_sum _ _
  simp_rw [hexp]
  rw [← h]
  have hbool (i : ι) : (∑ b : Bool, Real.exp (sign b * v i)) = 2 * Real.cosh (v i) := by
    simp [sign, Real.cosh_eq]
    ring
  simp_rw [hbool]
  rw [Finset.prod_mul_distrib]
  simp

theorem sign_exp_sum_le (v : ι → ℝ) :
    (∑ s : ι → Bool, Real.exp (∑ i, sign (s i) * v i)) ≤
      (2 : ℝ) ^ Fintype.card ι * Real.exp ((∑ i, v i ^ 2) / 2) := by
  rw [sign_exp_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∏ i, Real.cosh (v i) ≤ ∏ i, Real.exp (v i ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i _; exact (Real.cosh_pos _).le
      · intro i _; exact Real.cosh_le_exp_half_sq _
    _ = Real.exp ((∑ i, v i ^ 2) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_div]

section InvariantMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exp_inner_integrable (μ : Measure E) [IsFiniteMeasure μ]
    (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1) (x : E) (t : ℝ) :
    Integrable (fun u => Real.exp (t * inner ℝ u x)) μ := by
  apply (integrable_const (Real.exp (|t| * ‖x‖))).mono' (by fun_prop)
  filter_upwards [unit_norm] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hi := abs_real_inner_le_norm u x
  rw [hu, one_mul] at hi
  exact (le_abs_self (t * inner ℝ u x)).trans
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg t))

theorem exp_inner_integral_eq_of_norm_eq (μ : Measure E)
    (invariant : WC.Sphere.RotationallyInvariant μ) {x y : E} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    (∫ u, Real.exp (t * inner ℝ u x) ∂μ) = ∫ u, Real.exp (t * inner ℝ u y) ∂μ := by
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, invariant e⟩
  have hi := hp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun u => Real.exp (t * inner ℝ u y))
  have hfun : (fun u => Real.exp (t * inner ℝ (e u) y)) =
      (fun u => Real.exp (t * inner ℝ u x)) := by
    funext u
    rw [← he, e.inner_map_map]
  rw [hfun] at hi
  exact hi

/-- Exact dimension-normalized MGF bound, obtained by averaging the
orthogonal coordinate sign group after rotating the target to a flat vector. -/
theorem sphere_mgf_le (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : WC.Sphere.RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E) (t : ℝ) :
    (∫ u, Real.exp (t * inner ℝ u x) ∂μ) ≤ Real.exp (t ^ 2 * ‖x‖ ^ 2 / (2 * (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  let c : ℝ := ‖x‖ / Real.sqrt (d : ℝ)
  let flat : E := b.repr.symm (WithLp.toLp 2 (fun _ : Fin d => c))
  have hflat : ‖flat‖ = ‖x‖ := by
    have hs : ‖flat‖ ^ 2 = ‖x‖ ^ 2 := by
      dsimp [flat]
      rw [b.repr.symm.norm_map, EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.toLp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [c]
      rw [div_pow, Real.sq_sqrt hdR.le]
      field_simp
    nlinarith [norm_nonneg flat, norm_nonneg x]
  let flip (s : Fin d → Bool) : E ≃ₗᵢ[ℝ] E :=
    b.repr.trans ((signFlip s).trans b.repr.symm)
  let integrand (s : Fin d → Bool) (u : E) := Real.exp (t * inner ℝ (flip s u) flat)
  have hflipNorm (s : Fin d → Bool) : ∀ᵐ u ∂μ, ‖flip s u‖ = 1 := by
    filter_upwards [unit_norm] with u hu
    rw [(flip s).norm_map, hu]
  have hint (s : Fin d → Bool) : Integrable (integrand s) μ := by
    apply (integrable_const (Real.exp (|t| * ‖flat‖))).mono' (by dsimp [integrand]; fun_prop)
    filter_upwards [hflipNorm s] with u hu
    dsimp [integrand]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hi := abs_real_inner_le_norm (flip s u) flat
    rw [hu, one_mul] at hi
    exact (le_abs_self (t * inner ℝ (flip s u) flat)).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg t))
  have hsame (s : Fin d → Bool) : (∫ u, integrand s u ∂μ) =
      ∫ u, Real.exp (t * inner ℝ u flat) ∂μ := by
    have hp : MeasurePreserving (flip s) μ μ := ⟨(flip s).continuous.measurable, invariant (flip s)⟩
    exact hp.integral_comp (flip s).toHomeomorph.measurableEmbedding
      (fun u => Real.exp (t * inner ℝ u flat))
  have hpoint : ∀ᵐ u ∂μ, (∑ s : Fin d → Bool, integrand s u) ≤
      (2 : ℝ) ^ d * Real.exp (t ^ 2 * ‖x‖ ^ 2 / (2 * (d : ℝ))) := by
    filter_upwards [unit_norm] with u hu
    have hcoords : ∑ i : Fin d, (b.repr u i) ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map, hu]
      norm_num
    have hinner (s : Fin d → Bool) : t * inner ℝ (flip s u) flat =
        ∑ i : Fin d, sign (s i) * (t * c * b.repr u i) := by
      rw [← b.repr.inner_map_map]
      simp only [flip, flat, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      change t * inner ℝ (signFlip s (b.repr u)) (WithLp.toLp 2 (fun _ : Fin d => c)) = _
      simp only [PiLp.inner_apply, Real.inner_apply, signFlip_apply, PiLp.toLp_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hvsum : (∑ i : Fin d, (t * c * b.repr u i) ^ 2) / 2 =
        t ^ 2 * ‖x‖ ^ 2 / (2 * (d : ℝ)) := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, hcoords, mul_one]
      dsimp [c]
      rw [div_pow, Real.sq_sqrt hdR.le]
      ring
    have hh := sign_exp_sum_le (fun i : Fin d => t * c * b.repr u i)
    simp only [Fintype.card_fin] at hh
    dsimp [integrand]
    simp_rw [hinner]
    rwa [hvsum] at hh
  have havg : (2 : ℝ) ^ d * (∫ u, Real.exp (t * inner ℝ u flat) ∂μ) =
      ∫ u, ∑ s : Fin d → Bool, integrand s u ∂μ := by
    rw [integral_finsetSum _ (fun s _ => hint s)]
    simp_rw [hsame]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hb := integral_mono_ae (integrable_finsetSum _ (fun s _ => hint s))
    (integrable_const ((2 : ℝ) ^ d * Real.exp (t ^ 2 * ‖x‖ ^ 2 / (2 * (d : ℝ))))) hpoint
  rw [← havg] at hb
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hb
  have hfinal := (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℝ) < 2) d)).mp hb
  rw [exp_inner_integral_eq_of_norm_eq μ invariant hflat.symm t]
  exact hfinal

theorem sphere_mgf_le_of_norm_le (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : WC.Sphere.RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E)
    {B : ℝ} (hB : 0 ≤ B) (hx : ‖x‖ ≤ B) (t : ℝ) :
    (∫ u, Real.exp (t * inner ℝ u x) ∂μ) ≤ Real.exp (t ^ 2 * B ^ 2 / (2 * (d : ℝ))) := by
  apply (sphere_mgf_le μ invariant unit_norm hd b x t).trans
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg x) hB).mpr hx) (sq_nonneg t)

theorem sphere_projection_tail_one_real (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : WC.Sphere.RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E)
    {B a : ℝ} (hB : 0 < B) (hx : ‖x‖ ≤ B) (ha : 0 < a) :
    μ.real {u | a ≤ inner ℝ u x} ≤ Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
  let t : ℝ := (d : ℝ) * a / B ^ 2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm := ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := fun u : E => inner ℝ u x)
    (μ := μ) a ht (exp_inner_integrable μ unit_norm x t)
  have hmgf := sphere_mgf_le_of_norm_le μ invariant unit_norm hd b x hB.le hx t
  have hcombined := hm.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (-t * a)).le)
  rw [← Real.exp_add] at hcombined
  have heq : -t * a + t ^ 2 * B ^ 2 / (2 * (d : ℝ)) =
      - (d : ℝ) * a ^ 2 / (2 * B ^ 2) := by
    dsimp [t]
    field_simp
    ring
  rwa [heq] at hcombined

/-- A genuine spherical cap bound at the closed threshold `a ≤ |inner|`.
The closed bad event yields the strict small-coordinate event required by
the MP manuscript without any halving of the tolerance. -/
theorem sphere_projection_tail_real (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : WC.Sphere.RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E)
    {B a : ℝ} (hB : 0 < B) (hx : ‖x‖ ≤ B) (ha : 0 < a) :
    μ.real {u | a ≤ |inner ℝ u x|} ≤ 2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2)) := by
  have hpos := sphere_projection_tail_one_real μ invariant unit_norm hd b x hB hx ha
  have hneg := sphere_projection_tail_one_real μ invariant unit_norm hd b (-x) hB
    (by simpa only [norm_neg] using hx) ha
  have heq : {u : E | a ≤ |inner ℝ u x|} =
      {u | a ≤ inner ℝ u x} ∪ {u | a ≤ inner ℝ u (-x)} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, inner_neg_right]
    rcases le_total 0 (inner ℝ u x) with h | h
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · intro hh; rcases hh with hh | hh <;> linarith
    · rw [abs_of_nonpos h]
      constructor
      · exact Or.inr
      · intro hh; rcases hh with hh | hh <;> linarith
  rw [heq]
  exact (measureReal_union_le _ _).trans (by linarith)

theorem sphere_projection_tail (μ : Measure E) [IsProbabilityMeasure μ]
    (invariant : WC.Sphere.RotationallyInvariant μ) (unit_norm : ∀ᵐ u ∂μ, ‖u‖ = 1)
    {d : ℕ} (hd : 0 < d) (b : OrthonormalBasis (Fin d) ℝ E) (x : E)
    {B a : ℝ} (hB : 0 < B) (hx : ‖x‖ ≤ B) (ha : 0 < a) :
    μ {u | a ≤ |inner ℝ u x|} ≤
      ENNReal.ofReal (2 * Real.exp (- (d : ℝ) * a ^ 2 / (2 * B ^ 2))) := by
  have h := ENNReal.ofReal_le_ofReal (sphere_projection_tail_real μ invariant unit_norm hd b x hB hx ha)
  rwa [ofReal_measureReal] at h

end InvariantMeasure

end MP.Concentration
