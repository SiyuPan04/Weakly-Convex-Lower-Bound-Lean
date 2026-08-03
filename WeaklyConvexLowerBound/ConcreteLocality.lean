import WeaklyConvexLowerBound.FormulaLocality
import WeaklyConvexLowerBound.WeakSubdifferential

/-!
# Semantic assembly of condition (C2)

The combinatorial locality theorem is already unconditional.  This short
module records the exact analytic interface: inclusion of every standard
full-subdifferential reply in the general formula model closes C2.
-/

namespace WeaklyConvexLowerBound

noncomputable section

theorem hardValue_fullSubdiff_locality_of_formula_inclusion {M N : Nat}
    (hA : Admissible M N)
    (hformula : ∀ z g,
      g ∈ fullSubdiff 1 (hardValue : BlockVec M N → ℝ) z →
        GeneralHardFormulaReply z g) :
    HasDiagonalLocality (relayDelay N)
      (fullSubdiff 1 (hardValue : BlockVec M N → ℝ)) := by
  intro t z hz g hg
  exact generalHardFormulaReply_locality hA hz (hformula z g hg)

end

end WeaklyConvexLowerBound

