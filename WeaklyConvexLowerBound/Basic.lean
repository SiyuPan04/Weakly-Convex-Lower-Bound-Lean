import WeaklyConvexLowerBound.Foundation.Euclidean

/-!
# Basic finite-dimensional model for the weakly convex lower-bound manuscript

The paper identifies `R^(M*N)` with `M` blocks of `N` coordinates.  We use
the definitionally equivalent nested Pi type, which keeps all block and
coordinate indices in bounds.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- A real vector with `M` blocks and `N` coordinates in every block. -/
abbrev BlockVec (M N : Nat) := Fin M → Fin N → ℝ

/-- Squared Euclidean norm, written without square roots for arithmetic proofs. -/
def blockSq {M N : Nat} (z : BlockVec M N) : ℝ :=
  ∑ m, ∑ j, (z m j) ^ 2

/-- Euclidean inner product on block vectors. -/
def blockDot {M N : Nat} (x y : BlockVec M N) : ℝ :=
  ∑ m, ∑ j, x m j * y m j

/-- The paper's admissibility regime (`N ≥ 60` and `2 ≤ M ≤ N/12`). -/
structure Admissible (M N : Nat) : Prop where
  N_ge : 60 ≤ N
  M_ge : 2 ≤ M
  twelve_M_le : 12 * M ≤ N

theorem Admissible.N_pos {M N : Nat} (h : Admissible M N) : 0 < N := by
  have hN := h.N_ge
  omega

theorem Admissible.M_pos {M N : Nat} (h : Admissible M N) : 0 < M := by
  have hM := h.M_ge
  omega

theorem blockSq_nonneg {M N : Nat} (z : BlockVec M N) : 0 ≤ blockSq z := by
  unfold blockSq
  exact Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (z m j)

/-- Coordinate-prefix support inside one block. -/
def PrefixSupported {N : Nat} (k : Nat) (u : Fin N → ℝ) : Prop :=
  ∀ j, k ≤ j.1 → u j = 0

/-- The diagonal level assigned in TeX line 1503, using zero-based indices. -/
def level (L : Nat) (m j : Nat) : Nat := m * L + j

/-- Coordinates visible through diagonal level `t`. -/
def VisibleAt {M N : Nat} (L t : Nat) (z : BlockVec M N) : Prop :=
  ∀ m j, t < level L m.1 j.1 → z m j = 0

end

end WeaklyConvexLowerBound


