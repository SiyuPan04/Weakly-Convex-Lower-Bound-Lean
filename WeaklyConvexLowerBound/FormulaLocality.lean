import WeaklyConvexLowerBound.Filtration
import WeaklyConvexLowerBound.Framework
import WeaklyConvexLowerBound.HardFormulaReply
import WeaklyConvexLowerBound.Variational
import WeaklyConvexLowerBound.Regularity

/-!
# Locality of every variational formula reply

Condition (C2) also has to cover the zero-activation case, where the outer
support problem can have many maximizers.  This file therefore uses an
arbitrary active feasible outer weight rather than the canonical positive-
activation weight from `HardFormulaReply`.
-/

namespace WeaklyConvexLowerBound

noncomputable section

open scoped BigOperators

/-- A weight solves the outer support problem at the score vector of `z`. -/
def ActiveOuterWeight {M N : Nat} (z : BlockVec M N)
    (w : Fin M → ℝ) : Prop :=
  FeasibleOuterWeight w ∧
    outerDot w (fun m => sigmaScore z m) = activationNorm z

/-- The block formula for an arbitrary active outer weight. -/
structure GeneralHardFormulaReply {M N : Nat}
    (z g : BlockVec M N) where
  w : Fin M → ℝ
  active : ActiveOuterWeight z w
  u : BlockVec M N
  u_subgradient : ∀ m, PhiSubgradient (z m) (u m)
  g_eq : ∀ m j, g m j =
    (2 / (N : ℝ)) *
      (w m * u m j - (1 - nextOuterWeight w m) * psiGrad (z m) j)

theorem activeWeight_eq_canonicalOuterWeight {M N : Nat}
    (z : BlockVec M N) :
    activeWeight z = canonicalOuterWeight (fun m => sigmaScore z m) := by
  funext m
  unfold activeWeight canonicalOuterWeight
  rw [activationNorm_eq_positiveNorm]

/-- At positive activation, the canonical terminal-reply model is a special
case of the arbitrary-active-weight model used for locality. -/
def HardFormulaReply.toGeneral {M N : Nat} {z g : BlockVec M N}
    (reply : HardFormulaReply z g) :
    GeneralHardFormulaReply z g where
  w := activeWeight z
  active := by
    constructor
    · rw [activeWeight_eq_canonicalOuterWeight]
      exact canonicalOuterWeight_feasible _
    · rw [activeWeight_eq_canonicalOuterWeight,
        canonicalOuterWeight_dot, ← activationNorm_eq_positiveNorm]
  u := reply.u
  u_subgradient := reply.u_subgradient
  g_eq := by
    intro m j
    simpa [netCoefficient, nextActiveWeight, nextOuterWeight] using
      reply.g_eq m j

def dropOuterWeight {M : Nat} (w : Fin M → ℝ) (m : Fin M) : Fin M → ℝ :=
  fun i => if i = m then 0 else w i

theorem outerDot_dropOuterWeight {M : Nat}
    (w s : Fin M → ℝ) (m : Fin M) :
    outerDot (dropOuterWeight w m) s = outerDot w s - w m * s m := by
  classical
  unfold outerDot dropOuterWeight
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun i : Fin M => w i * s i) (Finset.mem_univ m)
  calc
    (∑ i : Fin M, (if i = m then 0 else w i) * s i) =
        ∑ i ∈ (Finset.univ.erase m), w i * s i := by
      have hdrop := Finset.sum_erase_add (s := Finset.univ)
        (f := fun i : Fin M => (if i = m then 0 else w i) * s i)
        (Finset.mem_univ m)
      calc
        (∑ i : Fin M, (if i = m then 0 else w i) * s i) =
            (∑ i ∈ Finset.univ.erase m,
              (if i = m then 0 else w i) * s i) +
              (if m = m then 0 else w m) * s m := hdrop.symm
        _ = ∑ i ∈ Finset.univ.erase m, w i * s i := by
          simp only [if_pos, zero_mul, add_zero]
          apply Finset.sum_congr rfl
          intro i hi
          have him : i ≠ m := Finset.ne_of_mem_erase hi
          simp [him]
    _ = outerDot w s - w m * s m := by
      unfold outerDot
      linarith

theorem feasible_dropOuterWeight {M : Nat} {w : Fin M → ℝ}
    (hw : FeasibleOuterWeight w) (m : Fin M) :
    FeasibleOuterWeight (dropOuterWeight w m) := by
  constructor
  · intro i
    unfold dropOuterWeight
    split
    · norm_num
    · exact hw.1 i
  · calc
      (∑ i, (dropOuterWeight w m i) ^ 2) ≤ ∑ i, (w i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases him : i = m
        · subst i
          simpa [dropOuterWeight] using sq_nonneg (w m)
        · simp [dropOuterWeight, him]
      _ ≤ 1 := hw.2

/-- Any nonzero active weight can occur only on a nonnegative phase score.
This includes the `activationNorm = 0` case needed by C2. -/
theorem ActiveOuterWeight.score_nonneg_of_weight_ne_zero {M N : Nat}
    {z : BlockVec M N} {w : Fin M → ℝ}
    (hw : ActiveOuterWeight z w) (m : Fin M) (hwm : w m ≠ 0) :
    0 ≤ sigmaScore z m := by
  by_contra hs
  have hsneg : sigmaScore z m < 0 := lt_of_not_ge hs
  have hwpos : 0 < w m := lt_of_le_of_ne (hw.1.1 m) (Ne.symm hwm)
  let w' := dropOuterWeight w m
  have hw' : FeasibleOuterWeight w' := feasible_dropOuterWeight hw.1 m
  have hupper := outerDot_le_positiveNorm
    (w := w') (s := fun i => sigmaScore z i) hw'
  have hnorm : positiveNorm (fun i => sigmaScore z i) = activationNorm z := by
    exact (activationNorm_eq_positiveNorm z).symm
  rw [outerDot_dropOuterWeight, hw.2, hnorm] at hupper
  nlinarith

/-! ## Prefix progress estimate -/

private theorem sum_prefix_indicator {N k : Nat} (hk : k ≤ N) :
    (∑ j : Fin N, if j.1 < k then (1 : ℝ) else 0) = k := by
  change (∑ j : Fin N,
    (fun i : Nat => if i < k then (1 : ℝ) else 0) j.1) = k
  rw [Fin.sum_univ_eq_sum_range
    (fun i : Nat => if i < k then (1 : ℝ) else 0) N]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range N).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp
    omega
  rw [hfilter]
  simp

/-- If only the first `k` coordinates can be nonzero, progress is at most
`k/N`. -/
theorem psi_le_prefix {N k : Nat} (hN : 0 < N) (hk : k ≤ N)
    {u : Fin N → ℝ} (hu : PrefixSupported k u) :
    psi u ≤ (k : ℝ) / (N : ℝ) := by
  have hterm (j : Fin N) :
      q ((N : ℝ) * u j / 4) ≤ if j.1 < k then (1 : ℝ) else 0 := by
    by_cases hj : j.1 < k
    · simp only [hj, if_pos]
      exact q_le_one _
    · simp only [hj]
      have huj : u j = 0 := hu j (Nat.le_of_not_gt hj)
      simp [huj]
  have hsum : (∑ j, q ((N : ℝ) * u j / 4)) ≤
      ∑ j : Fin N, if j.1 < k then (1 : ℝ) else 0 :=
    Finset.sum_le_sum fun j _ => hterm j
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold psi
  rw [div_le_iff₀ hNR]
  rw [sum_prefix_indicator hk] at hsum
  calc
    (∑ j, q ((N : ℝ) * u j / 4)) ≤ (k : ℝ) := hsum
    _ = (k : ℝ) / (N : ℝ) * (N : ℝ) := by
      field_simp

theorem relayDelay_lt {N : Nat} (hN : 0 < N) : relayDelay N < N := by
  unfold relayDelay
  omega

theorem relayDelay_ratio_le {N : Nat} (hN : 0 < N) :
    (relayDelay N : ℝ) / (N : ℝ) ≤ (3 : ℝ) / 16 := by
  have hmul : 16 * relayDelay N ≤ 3 * N := by
    unfold relayDelay
    omega
  have hmulR : (16 : ℝ) * (relayDelay N : ℝ) ≤ 3 * (N : ℝ) := by
    exact_mod_cast hmul
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [div_le_iff₀ hNR]
  linarith

theorem intercept_first_add_three_sixteenths_lt_five_fourths
    {N : Nat} (hN : 0 < N) :
    intercept N (firstCoord hN) + (3 : ℝ) / 16 < (5 : ℝ) / 4 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold intercept firstCoord
  simp only [Nat.cast_zero, sub_zero]
  have hfrac : ((N : ℝ) - 1) / (16 * (N : ℝ)) < (1 : ℝ) / 16 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * (N : ℝ))]
    nlinarith
  linarith

/-! ## Diagonal locality -/

private theorem fan_coordinate_zero_of_positive_index {M N t : Nat}
    (hN : 0 < N) {z g : BlockVec M N}
    (hz : Reachable (relayDelay N) t z)
    (reply : GeneralHardFormulaReply z g)
    (m : Fin M) (j : Fin N) (hjpos : 0 < j.1)
    (hlevel : t + 1 ≤ level (relayDelay N) m.1 j.1) :
    reply.u m j = 0 := by
  let k := j.1 - 1
  have hkN : k < N := by
    dsimp [k]
    omega
  have hzprefix : PrefixSupported k (z m) := by
    intro i hi
    apply hz m i
    unfold level at hlevel ⊢
    dsimp [k] at hi
    omega
  have hu := phiSubgradient_locality hN hkN hzprefix
    (reply.u_subgradient m)
  apply hu j
  dsimp [k]
  omega

private theorem unreached_zero_index_weight_zero {M N t : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hz : Reachable (relayDelay N) t z)
    (reply : GeneralHardFormulaReply z g)
    (m : Fin M)
    (hlevel : t + 1 ≤ level (relayDelay N) m.1 0) :
    reply.w m = 0 := by
  have hm0 : m.1 ≠ 0 := by
    intro hm
    simp [level, hm] at hlevel
  let mp : Fin M := ⟨m.1 - 1, by omega⟩
  have hbase : t + 1 ≤ m.1 * relayDelay N := by
    simpa [level] using hlevel
  have hmdecomp : m.1 = (m.1 - 1) + 1 := by omega
  have hblock : z m = 0 := by
    funext i
    apply hz m i
    unfold level at hlevel ⊢
    omega
  have hprevPrefix : PrefixSupported (relayDelay N) (z mp) := by
    intro i hi
    apply hz mp i
    have hbase' := hbase
    rw [hmdecomp, Nat.add_mul] at hbase'
    change t ≤ (m.1 - 1) * relayDelay N + i.1
    omega
  have hpsi : psi (z mp) ≤ (relayDelay N : ℝ) / (N : ℝ) :=
    psi_le_prefix hA.N_pos (Nat.le_of_lt (relayDelay_lt hA.N_pos)) hprevPrefix
  have hratio := relayDelay_ratio_le hA.N_pos
  have hprev : previousProgress z m = psi (z mp) := by
    simp only [previousProgress, dif_neg hm0]
    congr 1
  have hphi : phi (z m) = intercept N (firstCoord hA.N_pos) := by
    rw [hblock]
    exact phi_zero_eq_intercept_first hA.N_pos
  have hc := intercept_first_add_three_sixteenths_lt_five_fourths hA.N_pos
  have hsneg : sigmaScore z m < 0 := by
    unfold sigmaScore
    rw [hphi, hprev]
    linarith
  by_contra hw
  have hsnonneg := reply.active.score_nonneg_of_weight_ne_zero m hw
  linarith

/-- Every variational formula reply advances by at most one diagonal level.
This is the combinatorial heart of condition (C2), including arbitrary outer
maximizers at zero activation. -/
theorem generalHardFormulaReply_locality {M N t : Nat}
    (hA : Admissible M N) {z g : BlockVec M N}
    (hz : Reachable (relayDelay N) t z)
    (reply : GeneralHardFormulaReply z g) :
    Reachable (relayDelay N) (t + 1) g := by
  intro m j hlevel
  have hzj : z m j = 0 := hz m j (by omega)
  have hpsi : psiGrad (z m) j = 0 :=
    psiGrad_eq_zero_of_coord_eq_zero j hzj
  rw [reply.g_eq m j, hpsi]
  simp only [mul_zero, sub_zero, mul_eq_zero]
  right
  by_cases hj : j.1 = 0
  · have hw : reply.w m = 0 :=
      unreached_zero_index_weight_zero hA hz reply m (by simpa [hj] using hlevel)
    exact Or.inl hw
  · have hu : reply.u m j = 0 :=
      fan_coordinate_zero_of_positive_index hA.N_pos hz reply m j
        (Nat.pos_of_ne_zero hj) hlevel
    exact Or.inr hu

end

end WeaklyConvexLowerBound

