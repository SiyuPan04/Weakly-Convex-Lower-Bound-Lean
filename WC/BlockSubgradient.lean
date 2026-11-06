import WC.Block
import WC.Subgradient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The finite-coordinate block inequalities identify genuine Euclidean convex
subgradients. Convexity then turns the same support theorem into a theorem
about the Fréchet subdifferential used by the manuscript.
-/

noncomputable section

namespace WC

open scoped BigOperators

def euclideanTiltedBlock (N K m : ℕ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  tiltedBlock N K m (fun i => x i)

theorem convexOn_euclideanTiltedBlock (N K m : ℕ) :
    ConvexOn ℝ Set.univ (euclideanTiltedBlock N K m) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (convexOn_tiltedBlock N K m).2 (Set.mem_univ (fun i => x i))
    (Set.mem_univ (fun i => y i)) ha hb hab
  convert h using 1 <;> rfl

theorem convexSubgradient_euclideanTiltedBlock_iff {N K m : ℕ}
    (x g : EuclideanSpace ℝ (Fin N)) :
    ConvexSubgradient (euclideanTiltedBlock N K m) x g ↔
      IsTiltedBlockSubgradient K m (fun i => x i) (fun i => g i) := by
  constructor
  · intro h y
    have hy := h (WithLp.toLp 2 y)
    simpa [euclideanTiltedBlock, PiLp.inner_apply, PiLp.sub_apply, mul_comm] using hy
  · intro h y
    have hy := h (fun i => y i)
    simpa [euclideanTiltedBlock, PiLp.inner_apply, PiLp.sub_apply, mul_comm] using hy

theorem euclideanTiltedBlock_frechetSubgradient_locality {N K m : ℕ}
    (x g : EuclideanSpace ℝ (Fin N)) (k : Fin N)
    (htail : ∀ n : Fin N, k ≤ n → x n = 0)
    (hg : FrechetSubgradient (euclideanTiltedBlock N K m) x g)
    (n : Fin N) (hkn : k < n) : g n = 0 := by
  have hc := WC.ConvexOn.support_of_frechet (convexOn_euclideanTiltedBlock N K m) hg
  have hb := (convexSubgradient_euclideanTiltedBlock_iff x g).mp hc
  exact tiltedBlock_subgradient_locality (fun i => x i) (fun i => g i) k htail hb n hkn

end WC
