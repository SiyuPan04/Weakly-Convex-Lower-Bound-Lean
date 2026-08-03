import WeaklyConvexLowerBound.Basic

/-!
# The diagonal filtration

This file formalizes the zero-based indexing convention used in the
generalized zero-chain argument.  In particular, natural-number division is
the floor operation, so `relayDelay N = (3 * N) / 16` is the integer `L` from
the manuscript.
-/

namespace WeaklyConvexLowerBound

noncomputable section

/-- The relay delay `L = floor (3N/16)`. -/
def relayDelay (N : Nat) : Nat := (3 * N) / 16

/-- In the admissible range, six relay delays cover one whole block. -/
theorem le_six_mul_relayDelay {N : Nat} (hN : 60 ≤ N) :
    N ≤ 6 * relayDelay N := by
  unfold relayDelay
  omega

/-- Natural-number form of `L ≥ N/6`. -/
theorem div_six_le_relayDelay {N : Nat} (hN : 60 ≤ N) :
    N / 6 ≤ relayDelay N := by
  have h := le_six_mul_relayDelay hN
  omega

/-- Real-valued form of the manuscript inequality `L ≥ N/6`. -/
theorem one_six_mul_le_relayDelay {N : Nat} (hN : 60 ≤ N) :
    (N : ℝ) / 6 ≤ (relayDelay N : ℝ) := by
  have h := le_six_mul_relayDelay hN
  have h' : (N : ℝ) ≤ 6 * (relayDelay N : ℝ) := by
    exact_mod_cast h
  linarith

/-- Number of visible coordinates in zero-based block `m` through level `t`.

The visible coordinates in that block are exactly `0, ..., k-1`, where this
definition is the `k` in the paper's block-prefix description.
-/
def visiblePrefix (N L t m : Nat) : Nat :=
  min N (t + 1 - m * L)

theorem visiblePrefix_le (N L t m : Nat) : visiblePrefix N L t m ≤ N := by
  exact min_le_left _ _

/-- A coordinate is below the diagonal cutoff iff it lies in its block's
visible prefix. -/
theorem level_le_iff_lt_visiblePrefix {N L t m j : Nat} (hj : j < N) :
    level L m j ≤ t ↔ j < visiblePrefix N L t m := by
  simp only [visiblePrefix, level, lt_min_iff]
  omega

/-- The finite set of coordinates visible in block `m` through level `t`. -/
def visibleBlock (N L t m : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun j => j.1 < visiblePrefix N L t m

@[simp] theorem mem_visibleBlock {N L t m : Nat} {j : Fin N} :
    j ∈ visibleBlock N L t m ↔ level L m j.1 ≤ t := by
  simp only [visibleBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (level_le_iff_lt_visiblePrefix j.isLt).symm

/-- The diagonal visibility predicate from `Basic` is precisely prefix
support, with a possibly different prefix length in every block. -/
theorem visibleAt_iff_prefixSupported {M N L t : Nat} (z : BlockVec M N) :
    VisibleAt L t z ↔
      ∀ m : Fin M, PrefixSupported (visiblePrefix N L t m.1) (z m) := by
  constructor
  · intro hz m j hj
    apply hz m j
    by_contra hlevel
    have hle : level L m.1 j.1 ≤ t := Nat.le_of_not_gt hlevel
    have hlt := (level_le_iff_lt_visiblePrefix j.isLt).1 hle
    omega
  · intro hz m j hlevel
    apply hz m j
    have hnlt : ¬j.1 < visiblePrefix N L t m.1 := by
      intro hlt
      have hle := (level_le_iff_lt_visiblePrefix j.isLt).2 hlt
      omega
    omega

/-- The coordinate directions occurring at one exact diagonal level. -/
def layerCoordinates (M N L r : Nat) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => level L p.1.1 p.2.1 = r

@[simp] theorem mem_layerCoordinates {M N L r : Nat} {p : Fin M × Fin N} :
    p ∈ layerCoordinates M N L r ↔ level L p.1.1 p.2.1 = r := by
  simp [layerCoordinates]

private theorem layer_block_le_div {M N L r : Nat} (hL : 0 < L)
    {p : Fin M × Fin N} (hp : p ∈ layerCoordinates M N L r) :
    p.1.1 ≤ r / L := by
  apply (Nat.le_div_iff_mul_le hL).2
  have heq := (mem_layerCoordinates).1 hp
  simp only [level] at heq
  omega

private theorem layer_div_lt_block_add_six {M N L r : Nat}
    (hL : 0 < L) (hNL : N ≤ 6 * L)
    {p : Fin M × Fin N} (hp : p ∈ layerCoordinates M N L r) :
    r / L < p.1.1 + 6 := by
  have heq := (mem_layerCoordinates).1 hp
  have hqmul : (r / L) * L ≤ r := Nat.div_mul_le_self r L
  have hrlt : r < (p.1.1 + 6) * L := by
    calc
      r = p.1.1 * L + p.2.1 := by simpa [level] using heq.symm
      _ < p.1.1 * L + N := by omega
      _ ≤ p.1.1 * L + 6 * L := by omega
      _ = (p.1.1 + 6) * L := by ring
  exact (Nat.mul_lt_mul_right hL).1 (lt_of_le_of_lt hqmul hrlt)

/-- Every layer contains at most six coordinate directions.  This is the
exact finite-cardinality version of `dim E_r ≤ 6`. -/
theorem card_layerCoordinates_le_six {M N r : Nat} (hN : 60 ≤ N) :
    (layerCoordinates M N (relayDelay N) r).card ≤ 6 := by
  let L := relayDelay N
  have hNL : N ≤ 6 * L := by
    simpa [L] using le_six_mul_relayDelay hN
  have hL : 0 < L := by omega
  have hcard : (layerCoordinates M N L r).card ≤ (Finset.range 6).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : Fin M × Fin N => r / L - p.1.1) ?_ ?_
    · intro p hp
      change p ∈ layerCoordinates M N L r at hp
      change r / L - p.1.1 ∈ Finset.range 6
      rw [Finset.mem_range]
      have hupper := layer_div_lt_block_add_six hL hNL hp
      omega
    · intro p hp q hq heq
      change p ∈ layerCoordinates M N L r at hp
      change q ∈ layerCoordinates M N L r at hq
      change r / L - p.1.1 = r / L - q.1.1 at heq
      have hpLower := layer_block_le_div hL hp
      have hqLower := layer_block_le_div hL hq
      have hm : p.1.1 = q.1.1 := by
        calc
          p.1.1 = r / L - (r / L - p.1.1) :=
            (Nat.sub_sub_self hpLower).symm
          _ = r / L - (r / L - q.1.1) := by rw [heq]
          _ = q.1.1 := Nat.sub_sub_self hqLower
      have hpLevel := (mem_layerCoordinates).1 hp
      have hqLevel := (mem_layerCoordinates).1 hq
      have hj : p.2.1 = q.2.1 := by
        simp only [level] at hpLevel hqLevel
        rw [hm] at hpLevel
        omega
      exact Prod.ext (Fin.ext hm) (Fin.ext hj)
  simpa [L] using hcard

/-- The terminal diagonal level `H_{M,N}` from the manuscript. -/
def horizon (M N : Nat) : Nat :=
  (M - 1) * relayDelay N + N / 2

private theorem product_le_twelve_horizon {M N : Nat}
    (hM : 2 ≤ M) (hN : 60 ≤ N) : M * N ≤ 12 * horizon M N := by
  have hM' : M ≤ 2 * (M - 1) := by omega
  have hN' : N ≤ 6 * relayDelay N := le_six_mul_relayDelay hN
  calc
    M * N ≤ (2 * (M - 1)) * (6 * relayDelay N) := Nat.mul_le_mul hM' hN'
    _ = 12 * ((M - 1) * relayDelay N) := by ring
    _ ≤ 12 * horizon M N := by
      unfold horizon
      omega

/-- Natural-number form of `H_{M,N} ≥ MN/120`. -/
theorem product_div_120_le_horizon {M N : Nat}
    (hM : 2 ≤ M) (hN : 60 ≤ N) : M * N / 120 ≤ horizon M N := by
  have hprod := product_le_twelve_horizon hM hN
  apply (Nat.div_le_iff_le_mul (by omega : 0 < 120)).2
  omega

/-- Real-valued form of the manuscript inequality `H_{M,N} ≥ MN/120`. -/
theorem product_over_120_le_horizon {M N : Nat}
    (hM : 2 ≤ M) (hN : 60 ≤ N) :
    ((M * N : Nat) : ℝ) / 120 ≤ (horizon M N : ℝ) := by
  have hprod := product_le_twelve_horizon hM hN
  have hprod' : ((M * N : Nat) : ℝ) ≤ 12 * (horizon M N : ℝ) := by
    exact_mod_cast hprod
  linarith

end

end WeaklyConvexLowerBound

