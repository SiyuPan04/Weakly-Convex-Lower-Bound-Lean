import WC.UpperAlgorithm

/-! Finite convergence of the actual proximal outer iteration. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def proximalOuterIterate (ρ G ε : ℝ) (select : E → E) (L : ℕ) (x : E) : ℕ → E
  | 0 => x
  | k + 1 => proximalOuterUpdate ρ G ε select L (proximalOuterIterate ρ G ε select L x k)

theorem proximalOuterIterate_frozen {ρ G ε : ℝ} (select : E → E) (L : ℕ) (x : E)
    (k : ℕ)
    (hk : ‖proximalInnerAverage (proximalOuterIterate ρ G ε select L x k) ρ G select L -
      proximalOuterIterate ρ G ε select L x k‖ ≤ ε / (4 * ρ)) (r : ℕ) :
    proximalOuterIterate ρ G ε select L x (k + r) = proximalOuterIterate ρ G ε select L x k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, proximalOuterIterate, ih]
    exact if_pos hk

/-- A finite number of actual rounds produces a certified center. -/
theorem proximalOuterIterate_certifies [ProperSpace E] {ρ G ε Δ : ℝ} {f : E → ℝ}
    (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G) (hε : 0 < ε)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) (hgap : GapBound Δ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z)) {L R : ℕ}
    (hL : 0 < L) (hiterations : (2 : ℝ) ^ 14 * G ^ 2 ≤ (L : ℝ) * ε ^ 2)
    (hR : 0 < R) (hbudget : Δ ≤ (R : ℝ) * (ε ^ 2 / (32 * ρ))) :
    ‖proximalInnerAverage (proximalOuterIterate ρ G ε select L 0 R) ρ G select L -
      proximalOuterIterate ρ G ε select L 0 R‖ ≤ ε / (4 * ρ) := by
  let x := proximalOuterIterate ρ G ε select L (0 : E)
  let c : ℝ := ε ^ 2 / (32 * ρ)
  by_contra hfinal
  have hnot (k : ℕ) (hk : k < R) : ‖proximalInnerAverage (x k) ρ G select L - x k‖ > ε / (4 * ρ) := by
    by_contra hfail
    have hcert : ‖proximalInnerAverage (x k) ρ G select L - x k‖ ≤ ε / (4 * ρ) := le_of_not_gt hfail
    have heq := proximalOuterIterate_frozen select L (0 : E) k hcert (R - k)
    rw [Nat.add_sub_of_le hk.le] at heq
    apply hfinal
    rw [heq]
    exact hcert
  have hstep (k : ℕ) (hk : k < R) : c < f (x k) - f (x (k + 1)) := by
    have hd := (proximalInnerRound_dichotomy (x k) select hρ hG hε hlip hwc hselect hL hiterations).2 (hnot k hk)
    have hcertnot : ¬‖proximalInnerAverage (x k) ρ G select L - x k‖ ≤ ε / (4 * ρ) :=
      not_le_of_gt (hnot k hk)
    have heq : x (k + 1) = proximalInnerAverage (x k) ρ G select L := by
      change proximalOuterUpdate ρ G ε select L (x k) = _
      exact if_neg hcertnot
    rw [heq]
    exact hd
  have hsum : ∀ n ≤ R, (n : ℝ) * c ≤ f (x 0) - f (x n) ∧
      (0 < n → (n : ℝ) * c < f (x 0) - f (x n)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hprev := (ih (by omega)).1
      have hnext := hstep n (by omega)
      push_cast
      constructor
      · linarith
      · intro _; linarith
  have hlarge := (hsum R le_rfl).2 hR
  have hsmall := hgap (x R)
  change f (x 0) - f (x R) ≤ Δ at hsmall
  linarith

theorem proximalOuterIterate_stationary [ProperSpace E] {ρ G ε Δ : ℝ} {f : E → ℝ}
    (select : E → E) (hρ : 0 < ρ) (hG : 0 ≤ G) (hε : 0 < ε)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) (hgap : GapBound Δ f)
    (hselect : ∀ z, FrechetSubgradient f z (select z)) {L R : ℕ}
    (hL : 0 < L) (hiterations : (2 : ℝ) ^ 14 * G ^ 2 ≤ (L : ℝ) * ε ^ 2)
    (hR : 0 < R) (hbudget : Δ ≤ (R : ℝ) * (ε ^ 2 / (32 * ρ))) :
    ‖gradient (moreauEnvelope (1 / (2 * ρ)) f) (proximalOuterIterate ρ G ε select L 0 R)‖ ≤ ε := by
  have hcert := proximalOuterIterate_certifies select hρ hG hε hlip hwc hgap hselect hL hiterations hR hbudget
  have hg := (proximalInnerRound_dichotomy (proximalOuterIterate ρ G ε select L 0 R)
    select hρ hG hε hlip hwc hselect hL hiterations).1 hcert
  linarith

def innerCallCount (G ε : ℝ) : ℕ := ⌈(2 : ℝ) ^ 14 * (G ^ 2 / ε ^ 2)⌉₊
def outerRoundCount (ρ Δ ε : ℝ) : ℕ := ⌊32 * (ρ * Δ / ε ^ 2)⌋₊ + 1

theorem innerCallCount_pos {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) : 0 < innerCallCount G ε := by
  apply Nat.ceil_pos.mpr
  positivity

theorem innerCallCount_budget {G ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ 14 * G ^ 2 ≤ (innerCallCount G ε : ℝ) * ε ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil ((2 : ℝ) ^ 14 * (G ^ 2 / ε ^ 2))) (sq_nonneg ε)
  have heq : ((2 : ℝ) ^ 14 * (G ^ 2 / ε ^ 2)) * ε ^ 2 = (2 : ℝ) ^ 14 * G ^ 2 := by
    field_simp
  simpa only [heq, innerCallCount] using h

theorem outerRoundCount_budget {ρ Δ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Δ ≤ (outerRoundCount ρ Δ ε : ℝ) * (ε ^ 2 / (32 * ρ)) := by
  have h := Nat.lt_floor_add_one (32 * (ρ * Δ / ε ^ 2))
  have hpos : 0 < ε ^ 2 / (32 * ρ) := by positivity
  have hm := mul_lt_mul_of_pos_right h hpos
  have heq : (32 * (ρ * Δ / ε ^ 2)) * (ε ^ 2 / (32 * ρ)) = Δ := by field_simp
  rw [heq] at hm
  simpa only [outerRoundCount, Nat.cast_add, Nat.cast_one] using hm.le

end WC
