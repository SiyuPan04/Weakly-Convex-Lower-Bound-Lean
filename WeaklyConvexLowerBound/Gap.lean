import WeaklyConvexLowerBound.Basic

/-!
# Initial-gap certificate

This isolates the order-theoretic `inf` step at TeX lines 2108--2159.  It
also records all nonemptiness/boundedness hypotheses that are implicit in the
paper notation.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set

/-- A pointwise lower bound passes to the infimum of a nonempty range. -/
theorem lower_bound_le_sInf_range {α : Type*} [Nonempty α]
    (f : α → ℝ) (b : ℝ) (hlower : ∀ x, b ≤ f x) :
    b ≤ sInf (Set.range f) := by
  apply le_csInf
  · exact Set.range_nonempty f
  · rintro y ⟨x, rfl⟩
    exact hlower x

/-- The numerical final step in Proposition `prop:gap`. -/
theorem initial_gap_certificate {M N : Nat} (hM : 2 ≤ M) (hN : 0 < N)
    (f : BlockVec M N → ℝ)
    (hlower : ∀ z, -(2 * (M : ℝ) / N) ≤ f z)
    (hzero : f 0 ≤ 2 / (N : ℝ)) :
    f 0 - sInf (Set.range f) ≤ 3 * (M : ℝ) / N := by
  have hinf : -(2 * (M : ℝ) / N) ≤ sInf (Set.range f) :=
    lower_bound_le_sInf_range f _ hlower
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    f 0 - sInf (Set.range f) ≤ 2 / (N : ℝ) + 2 * (M : ℝ) / N := by
      linarith
    _ = (2 + 2 * (M : ℝ)) / N := by ring
    _ ≤ 3 * (M : ℝ) / N :=
      (div_le_div_iff_of_pos_right hNreal).2 (by linarith)

/-- Strict origin evaluation, as obtained in the manuscript, is more than
enough for the non-strict certificate used by the class definition. -/
theorem initial_gap_certificate_of_lt {M N : Nat}
    (hM : 2 ≤ M) (hN : 0 < N)
    (f : BlockVec M N → ℝ)
    (hlower : ∀ z, -(2 * (M : ℝ) / N) ≤ f z)
    (hzero : f 0 < 2 / (N : ℝ)) :
    f 0 - sInf (Set.range f) ≤ 3 * (M : ℝ) / N :=
  initial_gap_certificate hM hN f hlower hzero.le

end

end WeaklyConvexLowerBound

