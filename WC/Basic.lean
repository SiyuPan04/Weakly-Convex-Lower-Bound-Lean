import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Definitions from Section 2 of `snapshot/rand2_revised.tex`.
`GapBound` uses the equivalent pointwise formulation of the initial gap.
We prove its equivalence to the infimum formulation below, including boundedness.
`IsProxPoint` denotes a genuine global minimizer, not an oracle for one.
No existence, differentiability, or Moreau-gradient theorem is assumed here.
-/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def WeaklyConvex (ρ : ℝ) (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => f x + ρ / 2 * ‖x‖ ^ 2)

def GloballyLipschitz (G : ℝ) (f : E → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ G * ‖x - y‖

def GapBound (Δ : ℝ) (f : E → ℝ) : Prop :=
  ∀ x, f 0 - f x ≤ Δ

structure Admissible (G ρ Δ : ℝ) (f : E → ℝ) : Prop where
  weaklyConvex : WeaklyConvex ρ f
  lipschitz : GloballyLipschitz G f
  gap : GapBound Δ f

def proxObjective (lam : ℝ) (f : E → ℝ) (x y : E) : ℝ :=
  f y + ‖x - y‖ ^ 2 / (2 * lam)

def IsProxPoint (lam : ℝ) (f : E → ℝ) (x p : E) : Prop :=
  ∀ y, proxObjective lam f x p ≤ proxObjective lam f x y

def moreauEnvelope (lam : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  sInf (Set.range (proxObjective lam f x))

/-- The proximal residual. Its equality with the envelope gradient is a separate
analytic obligation, not built into the definition of `moreauEnvelope`. -/
def proxResidual (lam : ℝ) (x p : E) : E := (1 / lam) • (x - p)

omit [NormedSpace ℝ E] in
theorem GapBound.bddBelow {Δ : ℝ} {f : E → ℝ} (h : GapBound Δ f) :
    BddBelow (Set.range f) := by
  refine ⟨f 0 - Δ, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := h x
  linarith

theorem gapBound_iff_inf {Δ : ℝ} {f : E → ℝ} :
    GapBound Δ f ↔ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Δ := by
  constructor
  · intro h
    refine ⟨h.bddBelow, ?_⟩
    have hi : f 0 - Δ ≤ sInf (Set.range f) :=
      le_csInf (Set.range_nonempty f) (by rintro _ ⟨x, rfl⟩; have := h x; linarith)
    linarith
  · rintro ⟨hb, hΔ⟩ x
    have := csInf_le hb (Set.mem_range_self x)
    linarith

omit [NormedSpace ℝ E] in
theorem GapBound.mono {Δ Δ' : ℝ} {f : E → ℝ}
    (h : GapBound Δ f) (hΔ : Δ ≤ Δ') : GapBound Δ' f :=
  fun x => (h x).trans hΔ

omit [NormedSpace ℝ E] in
theorem GapBound.nonneg {Δ : ℝ} {f : E → ℝ} (h : GapBound Δ f) : 0 ≤ Δ := by
  simpa using h 0

/-- General vertical and spatial rescaling used in Lemma `lem:scaling`. -/
def scaleFunction (a b : ℝ) (f : E → ℝ) (x : E) : ℝ := a * f (b • x)

theorem gapBound_scale {a b Δ : ℝ} {f : E → ℝ}
    (ha : 0 ≤ a) (h : GapBound Δ f) : GapBound (a * Δ) (scaleFunction a b f) := by
  intro x
  simpa [scaleFunction, mul_sub] using mul_le_mul_of_nonneg_left (h (b • x)) ha

theorem lipschitz_scale {a b G : ℝ} {f : E → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : GloballyLipschitz G f) :
    GloballyLipschitz (a * b * G) (scaleFunction a b f) := by
  intro x y
  have hxy := mul_le_mul_of_nonneg_left (h (b • x) (b • y)) ha
  simpa [scaleFunction, ← mul_sub, ← smul_sub, abs_mul, abs_of_nonneg ha,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, mul_assoc, mul_left_comm,
    mul_comm] using hxy

theorem weaklyConvex_scale {a b ρ : ℝ} {f : E → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : WeaklyConvex ρ f) :
    WeaklyConvex (a * b ^ 2 * ρ) (scaleFunction a b f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hbase := h.2 (Set.mem_univ (b • x)) (Set.mem_univ (b • y)) hu hv huv
  have heq : b • (u • x + v • y) = u • (b • x) + v • (b • y) := by
    simp [smul_add, smul_smul, mul_comm]
  rw [← heq] at hbase
  have hmul := mul_le_mul_of_nonneg_left hbase ha
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, smul_eq_mul] at hmul
  dsimp [scaleFunction]
  nlinarith [hmul]

theorem admissible_scale {a b G ρ Δ : ℝ} {f : E → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Admissible G ρ Δ f) :
    Admissible (a * b * G) (a * b ^ 2 * ρ) (a * Δ) (scaleFunction a b f) :=
  ⟨weaklyConvex_scale ha hb h.weaklyConvex,
    lipschitz_scale ha hb h.lipschitz, gapBound_scale ha h.gap⟩

omit [NormedSpace ℝ E] in
/-- An actual minimizer realizes the infimum defining the envelope. -/
theorem IsProxPoint.envelope_eq {lam : ℝ} {f : E → ℝ} {x p : E}
    (hp : IsProxPoint lam f x p) :
    moreauEnvelope lam f x = proxObjective lam f x p := by
  apply le_antisymm
  · exact csInf_le ⟨proxObjective lam f x p, by rintro _ ⟨y, rfl⟩; exact hp y⟩
      (Set.mem_range_self p)
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨y, rfl⟩; exact hp y)

omit [NormedSpace ℝ E] in
/-- Proximal minimality alone gives the descent estimate used in the upper bound. -/
theorem IsProxPoint.descent {lam : ℝ} {f : E → ℝ} {x p : E}
    (hp : IsProxPoint lam f x p) :
    f p + ‖x - p‖ ^ 2 / (2 * lam) ≤ f x := by
  simpa [proxObjective] using hp x

end WC


