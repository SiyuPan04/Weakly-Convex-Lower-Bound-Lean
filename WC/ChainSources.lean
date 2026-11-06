import WC.RawLipschitz
import WC.MajorantMaximumRule

/-! The full source formula instantiated for the actual hard construction. -/

noncomputable section
namespace WC

theorem chainMajorant_subdifferential {M N : ℕ} (hN : 256 ≤ N) (x : ChainSpace M N) :
    subdifferential chainMajorant x = convexHull ℝ (sourceSlopes coupledFunction 2 x) := by
  have hNpos : 0 < N := by omega
  exact subdifferential_majorant_eq_convexHull
    (rawLipschitzConstant_nonneg M N) (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (by norm_num : (0 : ℝ) ≤ 2)
    (coupledFunction_global_lipschitz hNpos) (weaklyConvex_coupledFunction hNpos)
    (chainMajorant_finite hNpos) (chainMajorant_sources_nonempty hNpos)
    (fun z y hy => chain_source_radius hN hy) x

theorem chain_sourceSlopes_isCompact {M N : ℕ} (hN : 0 < N) (x : ChainSpace M N) :
    IsCompact (sourceSlopes coupledFunction 2 x) :=
  sourceSlopes_isCompact (rawLipschitzConstant_nonneg M N)
    (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (coupledFunction_global_lipschitz hN) (weaklyConvex_coupledFunction hN) x
    (chainMajorant_sources_isCompact hN x)

theorem chain_source_coord_le {M N : ℕ} (hN : 0 < N) {x y : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) : ∀ i, y i ≤ x i :=
  majorant_source_coord_le (by norm_num) (chainMajorant_finite hN)
    coupledFunction_coordinate_antitone hy

theorem chain_source_subgradient_norm_le {M N : ℕ} (hN : 0 < N) {x y v : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (hv : v ∈ subdifferential coupledFunction y) :
    ‖v‖ ≤ 2 :=
  source_subgradient_norm_le (by norm_num : (0 : ℝ) ≤ 9 / 2) (by norm_num)
    (chainMajorant_finite hN) hy
    ((weakSubgradient_iff_frechet (by norm_num) (weaklyConvex_coupledFunction hN)).mpr hv)

theorem chain_remote_source_subgradient {M N : ℕ} (hN : 0 < N) {x y v : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (hxy : x ≠ y)
    (hv : v ∈ subdifferential coupledFunction y) :
    v = (-2 / ‖x - y‖) • (x - y) :=
  remote_source_subgradient (chainMajorant_finite hN) hy hxy hv

theorem chain_source_support_equality {M N : ℕ} (hN : 0 < N) {x y v : ChainSpace M N}
    (hy : y ∈ majorantSources coupledFunction 2 x) (hv : v ∈ subdifferential coupledFunction y) :
    coupledFunction y + inner ℝ v (x - y) = chainMajorant x :=
  source_support_equality (chainMajorant_finite hN) hy hv

end WC
