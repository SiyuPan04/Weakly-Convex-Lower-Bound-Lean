import Mathlib

/-! # Elementary floor arithmetic -/

namespace WeaklyConvexLowerBound.Foundation

noncomputable section

/-- Once `a ≥ 2`, the natural-number floor of `a` loses at most a factor two. -/
theorem half_le_natFloor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have hfloor : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  linarith

end

end WeaklyConvexLowerBound.Foundation
