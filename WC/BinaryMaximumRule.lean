import WC.CompactMaximumRule
import Mathlib.Analysis.Convex.Join

/-! Exact complete-subdifferential calculus for a binary maximum. -/

noncomputable section
namespace WC

inductive BinaryIndex where
  | left
  | right
  deriving DecidableEq, Fintype

instance : Inhabited BinaryIndex := ⟨BinaryIndex.left⟩

instance : MetricSpace BinaryIndex :=
  MetricSpace.induced (fun a => (((Fintype.equivFin BinaryIndex) a).val : ℝ)) (by
    intro a b h
    apply (Fintype.equivFin BinaryIndex).injective
    apply Fin.ext
    exact Nat.cast_injective h) inferInstance

instance : DiscreteTopology BinaryIndex := by infer_instance
instance : CompactSpace BinaryIndex := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def binaryMaximumFamily (f g : E → ℝ) : BinaryIndex → E → ℝ
  | BinaryIndex.left => f
  | BinaryIndex.right => g

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem compactMaximum_binaryMaximumFamily (f g : E → ℝ) :
    compactMaximum (binaryMaximumFamily f g) = fun x => max (f x) (g x) := by
  funext x
  have hg : IsGreatest (Set.range (fun a => binaryMaximumFamily f g a x)) (max (f x) (g x)) := by
    constructor
    · by_cases h : f x ≤ g x
      · exact ⟨BinaryIndex.right, (max_eq_right h).symm⟩
      · exact ⟨BinaryIndex.left, (max_eq_left (le_of_not_ge h)).symm⟩
    · rintro _ ⟨a, rfl⟩
      cases a
      · exact le_max_left _ _
      · exact le_max_right _ _
  exact hg.csSup_eq

def binaryActiveSlopes (f g : E → ℝ) (x : E) : Set E :=
  {v | (f x = max (f x) (g x) ∧ v ∈ subdifferential f x) ∨
    (g x = max (f x) (g x) ∧ v ∈ subdifferential g x)}

theorem activeSlopes_binaryMaximumFamily (f g : E → ℝ) (x : E) :
    activeSlopes (binaryMaximumFamily f g) x = binaryActiveSlopes f g x := by
  ext v
  constructor
  · rintro ⟨a, ha, hv⟩
    rw [activeParameters, compactMaximum_binaryMaximumFamily] at ha
    cases a
    · exact Or.inl ⟨ha, hv⟩
    · exact Or.inr ⟨ha, hv⟩
  · rintro (⟨hf, hv⟩ | ⟨hg, hv⟩)
    · refine ⟨BinaryIndex.left, ?_, hv⟩
      change f x = compactMaximum (binaryMaximumFamily f g) x
      rwa [compactMaximum_binaryMaximumFamily]
    · refine ⟨BinaryIndex.right, ?_, hv⟩
      change g x = compactMaximum (binaryMaximumFamily f g) x
      rwa [compactMaximum_binaryMaximumFamily]

variable [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem subdifferential_max_eq_convexHull {f g : E → ℝ} {G ρ : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hfLip : GloballyLipschitz G f) (hgLip : GloballyLipschitz G g)
    (hfWC : WeaklyConvex ρ f) (hgWC : WeaklyConvex ρ g) (x : E) :
    subdifferential (fun y => max (f y) (g y)) x = convexHull ℝ (binaryActiveSlopes f g x) := by
  have hc : Continuous (fun p : BinaryIndex × E => binaryMaximumFamily f g p.1 p.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro a
    cases a
    · exact hfLip.continuous hG
    · exact hgLip.continuous hG
  have h := subdifferential_compactMaximum_eq_convexHull hG hρ hc
    (fun a => by cases a; exact hfLip; exact hgLip) (fun a => by cases a; exact hfWC; exact hgWC) x
  rwa [compactMaximum_binaryMaximumFamily, activeSlopes_binaryMaximumFamily] at h

theorem subdifferential_max_left_of_lt {f g : E → ℝ} {G ρ : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hfLip : GloballyLipschitz G f) (hgLip : GloballyLipschitz G g)
    (hfWC : WeaklyConvex ρ f) (hgWC : WeaklyConvex ρ g) {x : E} (hx : g x < f x) :
    subdifferential (fun y => max (f y) (g y)) x = subdifferential f x := by
  rw [subdifferential_max_eq_convexHull hG hρ hfLip hgLip hfWC hgWC]
  have heq : binaryActiveSlopes f g x = subdifferential f x := by
    ext v
    simp [binaryActiveSlopes, max_eq_left hx.le, ne_of_lt hx]
  rw [heq]
  exact (subdifferential_convex x hρ hfWC).convexHull_eq

theorem subdifferential_max_right_of_lt {f g : E → ℝ} {G ρ : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hfLip : GloballyLipschitz G f) (hgLip : GloballyLipschitz G g)
    (hfWC : WeaklyConvex ρ f) (hgWC : WeaklyConvex ρ g) {x : E} (hx : f x < g x) :
    subdifferential (fun y => max (f y) (g y)) x = subdifferential g x := by
  rw [subdifferential_max_eq_convexHull hG hρ hfLip hgLip hfWC hgWC]
  have heq : binaryActiveSlopes f g x = subdifferential g x := by
    ext v
    simp [binaryActiveSlopes, max_eq_right hx.le, ne_of_lt hx]
  rw [heq]
  exact (subdifferential_convex x hρ hgWC).convexHull_eq

theorem subdifferential_max_of_eq {f g : E → ℝ} {G ρ : ℝ}
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hfLip : GloballyLipschitz G f) (hgLip : GloballyLipschitz G g)
    (hfWC : WeaklyConvex ρ f) (hgWC : WeaklyConvex ρ g) {x : E} (hx : f x = g x) :
    subdifferential (fun y => max (f y) (g y)) x =
      convexHull ℝ (subdifferential f x ∪ subdifferential g x) := by
  rw [subdifferential_max_eq_convexHull hG hρ hfLip hgLip hfWC hgWC]
  congr 1
  ext v
  simp [binaryActiveSlopes, hx]

omit [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem convexHull_union_singleton_representation {s : Set E} (hs : Convex ℝ s) (hsne : s.Nonempty)
    (b : E) {v : E} (hv : v ∈ convexHull ℝ (s ∪ {b})) :
    ∃ (a : ℝ) (h : E), 0 ≤ a ∧ a ≤ 1 ∧ h ∈ s ∧ v = a • h + (1 - a) • b := by
  rw [hs.convexHull_union (convex_singleton b) hsne (Set.singleton_nonempty b)] at hv
  obtain ⟨h, hh, c, hc, hseg⟩ := mem_convexJoin.mp hv
  have hcb : c = b := hc
  subst c
  obtain ⟨a, d, ha, hd, had, hv⟩ := hseg
  refine ⟨a, h, ha, by linarith, hh, ?_⟩
  have hdeq : d = 1 - a := by linarith
  rw [hdeq] at hv
  exact hv.symm

end WC
