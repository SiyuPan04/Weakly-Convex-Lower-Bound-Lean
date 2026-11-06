import MP.Family

/-! The prescribed MP fixed-radius family, uniform in ambient dimension,
discharges every construction premise used in the scaling reduction. -/

noncomputable section
namespace MP
open WC

theorem uniformFamilies : WC.LowerReduction.UniformFamilies := by
  intro M N hN hM hMmax
  have hm : 0 < M := by omega
  have hn : 0 < N := by omega
  refine ⟨(M - 1) * stagger N, 4 * radialRadius M N, normalizedChainTolerance M N,
    mul_pos (by norm_num) (radialRadius_pos hm), normalizedChainTolerance_pos M N hn, ?_⟩
  intro d hd hdim
  letI : NeZero d := hd
  let e := coreEmbedding M N d (by omega : M * N ≤ d)
  exact ⟨chainFamily e hM hN hMmax, rfl, rfl⟩

end MP
