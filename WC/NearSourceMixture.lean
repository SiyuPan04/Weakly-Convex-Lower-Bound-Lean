import WC.RawBarrier
import WC.ChainSources

/-! The near-source mixture argument, using an actual tilted proximal minimizer. -/

noncomputable section
namespace WC
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def affineTilt (f : E → ℝ) (A z : E) (v : E) : ℝ := f v - inner ℝ A (v - z)

theorem affineTilt_weaklyConvex {f : E → ℝ} {ρ : ℝ} (hf : WeaklyConvex ρ f) (A z : E) :
    WeaklyConvex ρ (affineTilt f A z) := by
  have ha : ConvexOn ℝ Set.univ (fun v : E => -(inner ℝ A (v - z))) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, smul_eq_mul]
    have hc : (a + b) * inner ℝ A z = inner ℝ A z := by rw [hab, one_mul]
    nlinarith
  have h := weaklyConvex_add_convex_fn hf ha
  have heq : affineTilt f A z = (fun v => f v + -(inner ℝ A (v - z))) := by
    funext v
    rfl
  rw [heq]
  exact h

theorem affineTilt_lipschitz {f : E → ℝ} {G : ℝ} (hf : GloballyLipschitz G f) (A z : E) :
    GloballyLipschitz (G + ‖A‖) (affineTilt f A z) := by
  intro x y
  have heq : affineTilt f A z x - affineTilt f A z y = (f x - f y) - inner ℝ A (x - y) := by
    simp only [affineTilt, inner_sub_right]
    ring
  rw [heq]
  calc
    _ ≤ |f x - f y| + |inner ℝ A (x - y)| := abs_sub _ _
    _ ≤ G * ‖x - y‖ + ‖A‖ * ‖x - y‖ := add_le_add (hf x y) (abs_real_inner_le_norm _ _)
    _ = _ := by ring

theorem affineTilt_weakSubgradient {f : E → ℝ} {ρ : ℝ} {A z q v : E}
    (hv : WeakSubgradient ρ (affineTilt f A z) q v) :
    WeakSubgradient ρ f q (A + v) := by
  intro y
  have h := hv y
  simp only [affineTilt, inner_add_left, inner_sub_right] at h ⊢
  linarith

def mixtureVector {ι : Type*} [Fintype ι] (weights : ι → ℝ) (v : ι → E) : E := ∑ i, weights i • v i

theorem mixtureVector_norm_le_radius {ι : Type*} [Fintype ι] (weights : ι → ℝ) (v : ι → E)
    (hweights : ∀ i, 0 ≤ weights i) (hweightssum : ∑ i, weights i = 1) {r : ℝ} (hv : ∀ i, ‖v i‖ ≤ r) :
    ‖mixtureVector weights v‖ ≤ r := by
  unfold mixtureVector
  calc
    _ ≤ ∑ i, ‖weights i • v i‖ := norm_sum_le _ _
    _ = ∑ i, weights i * ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweights i)]
    _ ≤ ∑ i, weights i * r := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hweights i)
    _ = r := by rw [← Finset.sum_mul, hweightssum, one_mul]

theorem averaged_source_support {ι : Type*} [Fintype ι] {f : E → ℝ} {ρ F : ℝ}
    (weights : ι → ℝ) (hweights : ∀ i, 0 ≤ weights i) (hweightssum : ∑ i, weights i = 1)
    (y g : ι → E) (z : E)
    (hs : ∀ i, WeakSubgradient ρ f (y i) (g i))
    (hcontact : ∀ i, f (y i) + inner ℝ (g i) (z - y i) = F) (v : E) :
    F + inner ℝ (mixtureVector weights g - ρ • mixtureVector weights (fun i => z - y i)) (v - z) -
      ρ / 2 * ‖v - z‖ ^ 2 - ρ / 2 * ∑ i, weights i * ‖z - y i‖ ^ 2 ≤ f v := by
  have hi (i : ι) : F + inner ℝ (g i - ρ • (z - y i)) (v - z) -
      ρ / 2 * ‖v - z‖ ^ 2 - ρ / 2 * ‖z - y i‖ ^ 2 ≤ f v := by
    have h := hs i v
    have hn : ‖v - y i‖ ^ 2 = ‖v - z‖ ^ 2 + 2 * inner ℝ (z - y i) (v - z) + ‖z - y i‖ ^ 2 := by
      have hh := norm_add_sq_real (v - z) (z - y i)
      rw [sub_add_sub_cancel, real_inner_comm] at hh
      linarith
    have hin : inner ℝ (g i) (v - y i) = inner ℝ (g i) (v - z) + inner ℝ (g i) (z - y i) := by
      rw [← inner_add_right, sub_add_sub_cancel]
    rw [hn, hin] at h
    simp only [inner_sub_left, real_inner_smul_left] at h ⊢
    nlinarith [hcontact i]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hi i) (hweights i)
  have heq :
      (∑ i, weights i * (F + inner ℝ (g i - ρ • (z - y i)) (v - z) -
        ρ / 2 * ‖v - z‖ ^ 2 - ρ / 2 * ‖z - y i‖ ^ 2)) =
      F + inner ℝ (mixtureVector weights g - ρ • mixtureVector weights (fun i => z - y i)) (v - z) -
        ρ / 2 * ‖v - z‖ ^ 2 - ρ / 2 * ∑ i, weights i * ‖z - y i‖ ^ 2 := by
    simp only [mixtureVector, inner_sub_left, real_inner_smul_left, sum_inner,
      mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hweightssum, one_mul, Finset.mul_sum]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [heq, ← Finset.sum_mul, hweightssum, one_mul] at hsum
  exact hsum

theorem nearSourceMixture_lower_bound [ProperSpace E] {ι : Type*} [Fintype ι]
    {f : E → ℝ} {ρ G F r b : ℝ} (hρ : 0 < ρ) (hG : 0 ≤ G)
    (hLip : GloballyLipschitz G f) (hWC : WeaklyConvex ρ f) (hr : 0 ≤ r)
    (weights : ι → ℝ) (hweights : ∀ i, 0 ≤ weights i) (hweightssum : ∑ i, weights i = 1)
    (y g : ι → E) (z : E) (hnear : ∀ i, ‖z - y i‖ ≤ r)
    (hs : ∀ i, WeakSubgradient ρ f (y i) (g i))
    (hcontact : ∀ i, f (y i) + inner ℝ (g i) (z - y i) = F) (hdom : f z ≤ F)
    (hbarrier : ∀ q, ‖q - z‖ ≤ r → ∀ v ∈ subdifferential f q, b ≤ ‖v‖) :
    b - 3 * ρ * r ≤ ‖mixtureVector weights g‖ := by
  let barg := mixtureVector weights g
  let bard := mixtureVector weights (fun i => z - y i)
  let A := barg - ρ • bard
  let S := ∑ i, weights i * ‖z - y i‖ ^ 2
  have hS : S ≤ r ^ 2 := by
    dsimp [S]
    calc
      _ ≤ ∑ i, weights i * r ^ 2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hr).mpr (hnear i)) (hweights i)
      _ = _ := by rw [← Finset.sum_mul, hweightssum, one_mul]
  have hbard : ‖bard‖ ≤ r := mixtureVector_norm_le_radius weights _ hweights hweightssum hnear
  have htiltLip := affineTilt_lipschitz hLip A z
  have htiltWC := affineTilt_weaklyConvex hWC A z
  obtain ⟨q, hq⟩ := exists_quadraticMinimizer hρ (show 0 ≤ G + ‖A‖ by positivity) htiltLip z
  have hqprox : IsProxPoint (1 / (2 * ρ)) (affineTilt f A z) z q := by
    intro v
    rw [proxObjective_half_inv, proxObjective_half_inv]
    exact hq v
  have hsupport := averaged_source_support weights hweights hweightssum y g z hs hcontact q
  change F + inner ℝ A (q - z) - ρ / 2 * ‖q - z‖ ^ 2 - ρ / 2 * S ≤ f q at hsupport
  have hqval := hq z
  change affineTilt f A z q + ρ * ‖z - q‖ ^ 2 ≤ affineTilt f A z z + ρ * ‖z - z‖ ^ 2 at hqval
  simp only [affineTilt, sub_self, inner_zero_right, norm_zero, sub_zero] at hqval
  rw [norm_sub_rev z q] at hqval
  have hdsq : ‖q - z‖ ^ 2 ≤ S := by
    by_contra hfail
    have hp := mul_pos hρ (sub_pos.mpr (lt_of_not_ge hfail))
    nlinarith
  have hdist : ‖q - z‖ ≤ r := (sq_le_sq₀ (norm_nonneg _) hr).mp (hdsq.trans hS)
  have hsub := affineTilt_weakSubgradient (hqprox.weakSubgradient hρ htiltWC)
  have hqbarrier := hbarrier q hdist (A + (2 * ρ) • (z - q)) (hsub.frechet hρ.le)
  have hAnorm : ‖A‖ ≤ ‖barg‖ + ρ * r := by
    calc
      _ ≤ ‖barg‖ + ‖ρ • bard‖ := norm_sub_le _ _
      _ = ‖barg‖ + ρ * ‖bard‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hbard hρ.le)
  have hqnorm : ‖A + (2 * ρ) • (z - q)‖ ≤ ‖barg‖ + 3 * ρ * r := by
    calc
      _ ≤ ‖A‖ + ‖(2 * ρ) • (z - q)‖ := norm_add_le _ _
      _ = ‖A‖ + (2 * ρ) * ‖q - z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * ρ), norm_sub_rev z q]
      _ ≤ (‖barg‖ + ρ * r) + (2 * ρ) * r :=
        add_le_add hAnorm (mul_le_mul_of_nonneg_left hdist (by positivity))
      _ = _ := by ring
  change b - 3 * ρ * r ≤ ‖barg‖
  linarith

/-- The second assertion of Lemma `newrand:mixtures`, for actual sources and full subgradients. -/
theorem chain_nearSourceMixture_lower_bound {M N : ℕ} (hN : 0 < N)
    {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 ≤ r)
    (weights : ι → ℝ) (hweights : ∀ i, 0 ≤ weights i) (hweightssum : ∑ i, weights i = 1)
    (y g : ι → ChainSpace M N) (z : ChainSpace M N)
    (hsource : ∀ i, y i ∈ majorantSources coupledFunction 2 z)
    (hg : ∀ i, g i ∈ subdifferential coupledFunction (y i))
    (hnear : ∀ i, ‖z - y i‖ ≤ r)
    (hfar : ∀ q ∈ terminalRegion, r < ‖z - q‖) :
    1 / (4 * Real.sqrt (N : ℝ)) - 3 * (9 / 2 : ℝ) * r ≤ ‖mixtureVector weights g‖ := by
  apply nearSourceMixture_lower_bound (by norm_num : (0 : ℝ) < 9 / 2)
    (rawLipschitzConstant_nonneg M N) (coupledFunction_global_lipschitz hN)
    (weaklyConvex_coupledFunction hN) hr weights hweights hweightssum y g z hnear
  · intro i
    exact (weakSubgradient_iff_frechet (by norm_num : (0 : ℝ) ≤ 9 / 2)
      (weaklyConvex_coupledFunction hN)).mpr (hg i)
  · intro i
    exact chain_source_support_equality hN (hsource i) (hg i)
  · exact coupledFunction_le_chainMajorant hN z
  · intro q hdist v hv
    have hneq : ‖positiveCoupledScores q‖ ≠ 0 := by
      intro heq
      have hq := (positiveCoupledScores_norm_eq_zero_iff_terminalRegion hN q).mp heq
      have hdist' : ‖z - q‖ ≤ r := by simpa only [norm_sub_rev] using hdist
      linarith [hfar q hq]
    exact coupledFunction_subgradient_norm_barrier hN q
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hneq)) hv

end WC
