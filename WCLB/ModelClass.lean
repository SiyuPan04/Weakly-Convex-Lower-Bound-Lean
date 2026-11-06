import WCLB.Model

/-! The manuscript's class-indexed definition specializes exactly to the
all-algorithm, all-admissible-instance complexity used in `WCLB.main`. -/

noncomputable section
namespace WCLB.Model

theorem oracleComplexityOn_univ (G ρ Δ ε ν : ℝ) (hG : 0 ≤ G) (hρ : 0 ≤ ρ) :
    oracleComplexityOn G ρ Δ ε ν hG hρ Set.univ Set.univ =
      oracleComplexity G ρ Δ ε ν hG hρ := by
  unfold oracleComplexityOn oracleComplexity WC.Model.oracleComplexity
  apply le_antisymm
  · apply le_iInf
    intro A
    apply iInf_le_of_le ⟨A, Set.mem_univ _⟩
    apply iSup_le
    intro I
    exact le_iSup (fun J => WC.Model.hittingTime hG hρ A J ε ν) I.val
  · apply le_iInf
    intro A
    apply iInf_le_of_le A.val
    apply iSup_le
    intro I
    exact le_iSup (fun J : {J : Instance G ρ Δ // J ∈ (Set.univ : Set (Instance G ρ Δ))} =>
      WC.Model.hittingTime hG hρ A.val J.val ε ν) ⟨I, Set.mem_univ _⟩

end WCLB.Model
