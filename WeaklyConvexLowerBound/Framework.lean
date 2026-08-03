import WeaklyConvexLowerBound.Basic

/-!
# The abstract full-set zero-chain reduction

This file formalizes Condition (C2), the reachable-region induction, and the
queried-point use of Condition (C3).  The indexing is shifted by one:
`Reachable L t` is the paper's `V_{t-1}`.  Thus `Reachable L 0` contains only
the zero vector and `Reachable L H` is exactly the terminal region
`V_{H-1}`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open Set
open scoped BigOperators

/-- Coordinates with diagonal level strictly below `t` may be nonzero. -/
def Reachable {M N : Nat} (L t : Nat) (z : BlockVec M N) : Prop :=
  ∀ m j, t ≤ level L m.1 j.1 → z m j = 0

theorem reachable_zero {M N : Nat} (L t : Nat) :
    Reachable L t (0 : BlockVec M N) := by
  intro m j _
  rfl

theorem Reachable.mono {M N L a b : Nat} {z : BlockVec M N}
    (hab : a ≤ b) (hz : Reachable L a z) : Reachable L b z := by
  intro m j hj
  exact hz m j (hab.trans hj)

/-- Support of the entire set-valued oracle reply, as in TeX line 523. -/
def SetSupport {M N : Nat} (S : Set (BlockVec M N)) (p : Fin M × Fin N) : Prop :=
  ∃ g ∈ S, g p.1 p.2 ≠ 0

/-- A query sequence obeys the generalized full-subdifferential
zero-respecting rule. -/
structure FullSetZeroRespecting {M N : Nat}
    (oracle : BlockVec M N → Set (BlockVec M N))
    (query : Nat → BlockVec M N) : Prop where
  start : query 0 = 0
  respects : ∀ t p, query t p.1 p.2 ≠ 0 →
    ∃ s < t, SetSupport (oracle (query s)) p

/-- Condition (C2), in shifted indexing. -/
def HasDiagonalLocality {M N : Nat} (L : Nat)
    (oracle : BlockVec M N → Set (BlockVec M N)) : Prop :=
  ∀ t z, Reachable L t z → ∀ g ∈ oracle z, Reachable L (t + 1) g

/-- The full-set zero-respecting induction used at TeX lines 967--984. -/
theorem zeroRespecting_reachable {M N L : Nat}
    {oracle : BlockVec M N → Set (BlockVec M N)}
    {query : Nat → BlockVec M N}
    (hloc : HasDiagonalLocality L oracle)
    (hzr : FullSetZeroRespecting oracle query) :
    ∀ t, Reachable L t (query t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro m j hlevel
      by_contra hnzero
      obtain ⟨s, hst, g, hgmem, hgcoord⟩ := hzr.respects t (m, j) hnzero
      have hqs : Reachable L s (query s) := ih s hst
      have hgs : Reachable L (s + 1) g := hloc s (query s) hqs g hgmem
      have hslevel : s + 1 ≤ level L m.1 j.1 := by omega
      exact hgcoord (hgs m j hslevel)

/-- Squared-norm formulation of Euclidean Lipschitz continuity. -/
def EuclideanLipschitz {M N : Nat} (C : ℝ) (f : BlockVec M N → ℝ) : Prop :=
  ∀ x y, (f x - f y) ^ 2 ≤ C ^ 2 * blockSq (x - y)

/-- The paper's global weak-convexity definition, with the Euclidean
quadratic written explicitly rather than using the Pi type's sup norm. -/
def WeaklyConvex {M N : Nat} (rho : ℝ) (f : BlockVec M N → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun z => f z + rho / 2 * blockSq z)

/-- Conditions (C1)--(C4) in a type-correct package.  The concrete files
instantiate the oracle and stationarity map; the abstract reduction below
uses only `locality` and `terminal_failure`. -/
structure HardInstanceCertificate (M N : Nat) where
  admissible : Admissible M N
  f : BlockVec M N → ℝ
  oracle : BlockVec M N → Set (BlockVec M N)
  stationarity : BlockVec M N → ℝ
  L : Nat
  H : Nat
  finite_valued : ∀ z, ∃ r : ℝ, f z = r
  bounded_below : BddBelow (Set.range f)
  one_lipschitz : EuclideanLipschitz 1 f
  one_weaklyConvex : WeaklyConvex 1 f
  locality : HasDiagonalLocality L oracle
  horizon_lower : M * N ≤ 120 * H
  terminal_failure : ∀ z, Reachable L H z →
    1 / (8 * Real.sqrt N) < stationarity z
  initial_gap : f 0 - sInf (Set.range f) ≤ 3 * (M : ℝ) / N

/-- Every query through (and including) index `H` remains in the terminal
failure region.  This makes the off-by-one convention explicit. -/
theorem HardInstanceCertificate.query_failure_through_horizon {M N : Nat}
    (C : HardInstanceCertificate M N)
    {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting C.oracle query) :
    ∀ t ≤ C.H, 1 / (8 * Real.sqrt N) < C.stationarity (query t) := by
  intro t ht
  have hreach_t : Reachable C.L t (query t) :=
    zeroRespecting_reachable C.locality hzr t
  exact C.terminal_failure (query t) (hreach_t.mono ht)

/-- In particular, the first `H` queries (indices `0,...,H-1`) all fail. -/
theorem HardInstanceCertificate.query_failure_before_horizon {M N : Nat}
    (C : HardInstanceCertificate M N)
    {query : Nat → BlockVec M N}
    (hzr : FullSetZeroRespecting C.oracle query) :
    ∀ t < C.H, 1 / (8 * Real.sqrt N) < C.stationarity (query t) := by
  intro t ht
  exact C.query_failure_through_horizon hzr t (Nat.le_of_lt ht)

end

end WeaklyConvexLowerBound

