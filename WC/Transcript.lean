import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Deterministic transcript coupling

This file formalizes the deterministic induction in the proof of
`thm:abstract-randomized` (manuscript lines 1129–1179). A private seed and
all hidden parameters are fixed throughout the argument. On a successful
projection event, a simulator's replies equal the real oracle's replies
at the simulated queries; consequently the transcripts, queries, and any
prescribed final output coincide.

This does not construct the random-frame measure or prove a probability
bound. In particular, `simulation_agrees` below is an explicit hypothesis,
not a claim that the hard family satisfies robust oracle locality.
-/

namespace WC
namespace Transcript

variable {X R S O : Type*}

/-- A query rule receives the private seed and the ordered list of replies.
The round number is recoverable as the length of that list. -/
abbrev QueryRule (S R X : Type*) := S → List R → X

/-- A simulator may use the round, fixed seed, transcript, and query.
Hidden frame parameters can be fixed before specifying this map. -/
abbrev Simulator (S R X : Type*) := ℕ → S → List R → X → R

/-- The first `t` simulated replies, in chronological order. -/
def simulate (query : QueryRule S R X) (response : Simulator S R X)
    (seed : S) : ℕ → List R
  | 0 => []
  | t + 1 =>
    let previous := simulate query response seed t
    previous ++ [response t seed previous (query seed previous)]

/-- The first `t` replies obtained by querying an actual oracle. -/
def actual (query : QueryRule S R X) (oracle : X → R) (seed : S) : ℕ → List R :=
  simulate query (fun _ _ _ x => oracle x) seed

@[simp] theorem simulate_zero (query : QueryRule S R X)
    (response : Simulator S R X) (seed : S) :
    simulate query response seed 0 = [] := rfl

@[simp] theorem simulate_succ (query : QueryRule S R X)
    (response : Simulator S R X) (seed : S) (t : ℕ) :
    simulate query response seed (t + 1) =
      simulate query response seed t ++
        [response t seed (simulate query response seed t)
          (query seed (simulate query response seed t))] := rfl

@[simp] theorem actual_zero (query : QueryRule S R X)
    (oracle : X → R) (seed : S) : actual query oracle seed 0 = [] := rfl

@[simp] theorem actual_succ (query : QueryRule S R X)
    (oracle : X → R) (seed : S) (t : ℕ) :
    actual query oracle seed (t + 1) =
      actual query oracle seed t ++ [oracle (query seed (actual query oracle seed t))] :=
  rfl

@[simp] theorem simulate_length (query : QueryRule S R X)
    (response : Simulator S R X) (seed : S) (t : ℕ) :
    (simulate query response seed t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ih]

@[simp] theorem actual_length (query : QueryRule S R X)
    (oracle : X → R) (seed : S) (t : ℕ) :
    (actual query oracle seed t).length = t := by
  exact simulate_length query (fun _ _ _ x => oracle x) seed t

/-- Agreement is needed only on the simulated path, for rounds below `T`.
The induction does not assume agreement on arbitrary transcripts. -/
theorem coupling (query : QueryRule S R X) (oracle : X → R)
    (response : Simulator S R X) (seed : S) (T : ℕ)
    (simulation_agrees : ∀ t < T,
      response t seed (simulate query response seed t)
          (query seed (simulate query response seed t)) =
        oracle (query seed (simulate query response seed t))) :
    ∀ t ≤ T, actual query oracle seed t = simulate query response seed t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have previous := ih (Nat.le_trans (Nat.le_succ t) ht)
    have agrees := simulation_agrees t (Nat.lt_of_succ_le ht)
    rw [actual_succ, simulate_succ, previous, agrees]

/-- All queries through the candidate formed after the `T`th reply agree. -/
theorem queries_eq (query : QueryRule S R X) (oracle : X → R)
    (response : Simulator S R X) (seed : S) (T : ℕ)
    (simulation_agrees : ∀ t < T,
      response t seed (simulate query response seed t)
          (query seed (simulate query response seed t)) =
        oracle (query seed (simulate query response seed t)))
    (t : ℕ) (ht : t ≤ T) :
    query seed (actual query oracle seed t) =
      query seed (simulate query response seed t) := by
  rw [coupling query oracle response seed T simulation_agrees t ht]

/-- The final output can be any function of the seed and full transcript.
Its codomain need not be the query space. -/
theorem output_eq (query : QueryRule S R X) (oracle : X → R)
    (response : Simulator S R X) (seed : S) (T : ℕ)
    (output : S → List R → O)
    (simulation_agrees : ∀ t < T,
      response t seed (simulate query response seed t)
          (query seed (simulate query response seed t)) =
        oracle (query seed (simulate query response seed t))) :
    output seed (actual query oracle seed T) =
      output seed (simulate query response seed T) := by
  rw [coupling query oracle response seed T simulation_agrees T le_rfl]

/-- Transfer a simultaneous candidate property from simulation to reality.
For the rotation proof, `P` can express the terminal Moreau barrier.
The assumption for the final output is separate, since it is never queried. -/
theorem candidates_property (query : QueryRule S R X) (oracle : X → R)
    (response : Simulator S R X) (seed : S) (T : ℕ)
    (output : S → List R → X) (P : X → Prop)
    (simulation_agrees : ∀ t < T,
      response t seed (simulate query response seed t)
          (query seed (simulate query response seed t)) =
        oracle (query seed (simulate query response seed t)))
    (query_property : ∀ t < T, P (query seed (simulate query response seed t)))
    (output_property : P (output seed (simulate query response seed T))) :
    (∀ t < T, P (query seed (actual query oracle seed t))) ∧
      P (output seed (actual query oracle seed T)) := by
  constructor
  · intro t ht
    rw [queries_eq query oracle response seed T simulation_agrees t (Nat.le_of_lt ht)]
    exact query_property t ht
  · rw [output_eq query oracle response seed T output simulation_agrees]
    exact output_property

end Transcript
end WC
