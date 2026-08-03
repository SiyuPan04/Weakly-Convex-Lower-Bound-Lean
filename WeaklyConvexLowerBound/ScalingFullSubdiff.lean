import WeaklyConvexLowerBound.ScalingClosure
import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Exact full-subdifferential scaling

This is the set-valued form required by a full-subdifferential oracle: no
selection is made, and both inclusions are proved.
-/

namespace WeaklyConvexLowerBound

noncomputable section

def scaleSet {M N : Nat} (a : ℝ) (S : Set (BlockVec M N)) :
    Set (BlockVec M N) :=
  (fun g => a • g) '' S

theorem fullSubgradient_paper_scaled_iff {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (x g : BlockVec M N) :
    FullSubgradient rho
        (scaledFunction (G ^ 2 / rho) (rho / G) f) x (G • g) ↔
      FullSubgradient 1 f (scaleVec (rho / G) x) g := by
  rw [fullSubgradient_iff_qSubgradient,
    fullSubgradient_iff_qSubgradient]
  norm_num
  exact qSubgradient_paper_scaled_iff hG hrho x g

/-- Literal equality of the complete scaled reply set. -/
theorem fullSubdiff_paper_scaled_eq {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (x : BlockVec M N) :
    fullSubdiff rho
        (scaledFunction (G ^ 2 / rho) (rho / G) f) x =
      scaleSet G (fullSubdiff 1 f (scaleVec (rho / G) x)) := by
  ext h
  constructor
  · intro hh
    let g : BlockVec M N := G⁻¹ • h
    have hcancel : G • g = h := by
      ext m j
      simp [g]
      field_simp
    refine ⟨g, ?_, hcancel⟩
    change FullSubgradient 1 f (scaleVec (rho / G) x) g
    rw [← fullSubgradient_paper_scaled_iff hG hrho x g, hcancel]
    exact hh
  · rintro ⟨g, hg, rfl⟩
    change FullSubgradient rho
      (scaledFunction (G ^ 2 / rho) (rho / G) f) x (G • g)
    exact (fullSubgradient_paper_scaled_iff hG hrho x g).2 hg

end

end WeaklyConvexLowerBound

