import WC.AdjacentLocality
import WC.Numerics

/-! The actual full majorant subdifferential is supported on the next
diagonal. This is the source-sensitive locality needed by the simulator. -/

noncomputable section
namespace WC
open scoped BigOperators Classical

theorem chainMajorant_subgradient_diagonal_zero {M N : ℕ} (hM : 1 ≤ M) (hN : 256 ≤ N)
    (x : ChainSpace M N) (r : ℕ)
    (hidden : ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) →
      |x i| ≤ robustTolerance M N)
    {v : ChainSpace M N} (hv : v ∈ subdifferential chainMajorant x)
    (i : Fin M × Fin N) (hi : r < diagonalLevel N (i.1.val, i.2.val)) : v i = 0 := by
  have hNpos : 0 < N := by omega
  by_cases hstarted : i.1.val * stagger N ≤ r
  · let k : Fin N := ⟨r - i.1.val * stagger N, by
      have hh := i.2.isLt
      dsimp [diagonalLevel] at hi
      omega⟩
    have hklevel : diagonalLevel N (i.1.val, k.val) = r := by
      dsimp [diagonalLevel, k]
      omega
    have hki : k.val < i.2.val := by
      change r < i.1.val * stagger N + i.2.val at hi
      change r - i.1.val * stagger N < i.2.val
      omega
    exact chainMajorant_subgradient_hidden_later_zero hM hN hv i.1 k i.2 hki
      (hidden (i.1, k) (by rw [hklevel])) (hidden i hi.le)
  · have hfuture : r < i.1.val * stagger N := lt_of_not_ge hstarted
    have him : 0 < i.1.val := by
      by_contra h
      have hzero : i.1.val = 0 := by omega
      rw [hzero, zero_mul] at hfuture
      omega
    let front : Fin M := ⟨i.1.val - 1, by have hh := i.1.isLt; omega⟩
    let I : Finset (Fin N) := Finset.univ.filter (fun n => front.val * stagger N + n.val < r)
    have hnext : i.1.val = front.val + 1 := by dsimp [front]; omega
    have hI : I.card ≤ stagger N := by
      have hcard : I.card ≤ (Finset.range (stagger N)).card := by
        apply Finset.card_le_card_of_injOn (fun n : Fin N => n.val)
        · intro n hn
          have hn' : front.val * stagger N + n.val < r := (Finset.mem_filter.mp hn).2
          have hm : i.1.val * stagger N = front.val * stagger N + stagger N := by rw [hnext]; ring
          have hnsmall : n.val < stagger N := by omega
          exact Finset.mem_range.mpr hnsmall
        · intro n _ m _ heq
          exact Fin.ext heq
      simpa only [Finset.card_range] using hcard
    have hcard : 4 * I.card ≤ N := by
      have hstagger : 4 * stagger N ≤ N := by unfold stagger; omega
      omega
    have hfront (n : Fin N) (hn : n ∉ I) : |x (front, n)| ≤ robustTolerance M N := by
      have hlevel : r ≤ diagonalLevel N (front.val, n.val) := by
        have hh : ¬front.val * stagger N + n.val < r := by simpa [I] using hn
        dsimp [diagonalLevel]
        omega
      exact hidden (front, n) hlevel
    have hnextHidden (n : Fin N) : |x (i.1, n)| ≤ robustTolerance M N := by
      apply hidden
      dsimp [diagonalLevel]
      omega
    exact chainMajorant_subgradient_hidden_next_zero hM hN hv front i.1 hnext I hcard
      hfront hnextHidden i.2

def diagonalMask (M N r : ℕ) (x : ChainSpace M N) : ChainSpace M N :=
  WithLp.toLp 2 (fun i => if diagonalLevel N (i.1.val, i.2.val) < r then x i else 0)

@[simp] theorem diagonalMask_apply {M N r : ℕ} (x : ChainSpace M N) (i : Fin M × Fin N) :
    diagonalMask M N r x i = if diagonalLevel N (i.1.val, i.2.val) < r then x i else 0 := rfl

theorem diagonalMask_idempotent {M N r : ℕ} (x : ChainSpace M N) :
    diagonalMask M N r (diagonalMask M N r x) = diagonalMask M N r x := by
  apply PiLp.ext
  intro i
  simp only [diagonalMask_apply]
  split_ifs <;> rfl

theorem diagonalMask_inner_sub_zero {M N r : ℕ} (x v : ChainSpace M N)
    (hv : ∀ i : Fin M × Fin N, r ≤ diagonalLevel N (i.1.val, i.2.val) → v i = 0) :
    inner ℝ v (diagonalMask M N r x - x) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [PiLp.sub_apply, diagonalMask_apply, RCLike.inner_apply, conj_trivial]
  by_cases hi : diagonalLevel N (i.1.val, i.2.val) < r
  · rw [if_pos hi, sub_self, zero_mul]
  · rw [if_neg hi, hv i (by omega), mul_zero]

end WC
