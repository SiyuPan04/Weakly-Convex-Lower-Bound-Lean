import WeaklyConvexLowerBound.ExactScaling
import WeaklyConvexLowerBound.Regularity

/-!
# Analytic closure under the paper's coordinate scaling

`ExactScaling` contains the forward algebraic identities.  Here we close the
two-sided semantic statements needed by the oracle reduction: weak convexity
is preserved, and the complete quadratic-support reply set is carried
bijectively by the positive scalar map.
-/

namespace WeaklyConvexLowerBound

noncomputable section

theorem scaleVec_add {M N : Nat} (a : ℝ) (x y : BlockVec M N) :
    scaleVec a (x + y) = scaleVec a x + scaleVec a y := by
  ext m j
  simp [scaleVec]
  ring

theorem scaleVec_smul {M N : Nat} (a b : ℝ) (x : BlockVec M N) :
    scaleVec a (b • x) = b • scaleVec a x := by
  ext m j
  simp [scaleVec]
  ring

theorem scaleVec_combo {M N : Nat} (scale a b : ℝ)
    (x y : BlockVec M N) :
    scaleVec scale (a • x + b • y) =
      a • scaleVec scale x + b • scaleVec scale y := by
  rw [scaleVec_add, scaleVec_smul, scaleVec_smul]

/-- Generic closure of weak convexity under `x ↦ amp * f(scale*x)`.
The target modulus is exactly `amp * rho * scale²`. -/
theorem weaklyConvex_scaled {M N : Nat} {rho amp scale : ℝ}
    {f : BlockVec M N → ℝ} (hamp : 0 ≤ amp)
    (hf : WeaklyConvex rho f) :
    WeaklyConvex (amp * rho * scale ^ 2) (scaledFunction amp scale f) := by
  unfold WeaklyConvex
  constructor
  · exact convex_univ
  intro x _ y _ a b ha hb hab
  have hbase := hf.2 (Set.mem_univ (scaleVec scale x))
    (Set.mem_univ (scaleVec scale y)) ha hb hab
  have hscaled := mul_le_mul_of_nonneg_left hbase hamp
  rw [← scaleVec_combo] at hscaled
  have hrewrite (v : BlockVec M N) :
      scaledFunction amp scale f v +
          (amp * rho * scale ^ 2) / 2 * blockSq v =
        amp * (f (scaleVec scale v) + rho / 2 * blockSq (scaleVec scale v)) := by
    unfold scaledFunction
    rw [blockSq_scaleVec]
    ring
  change scaledFunction amp scale f (a • x + b • y) +
      (amp * rho * scale ^ 2) / 2 * blockSq (a • x + b • y) ≤
    a * (scaledFunction amp scale f x +
      (amp * rho * scale ^ 2) / 2 * blockSq x) +
    b * (scaledFunction amp scale f y +
      (amp * rho * scale ^ 2) / 2 * blockSq y)
  rw [hrewrite (a • x + b • y), hrewrite x, hrewrite y]
  simpa only [smul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Scaling by a nonzero scalar and then unscaling is the identity. -/
theorem unscaleVec_scaleVec {M N : Nat} {scale : ℝ} (hs : scale ≠ 0)
    (x : BlockVec M N) :
    unscaleVec scale (scaleVec scale x) = x := by
  ext m j
  simp [unscaleVec, scaleVec, hs]

theorem scaledFunction_cancel {M N : Nat} {amp scale : ℝ}
    (hamp : amp ≠ 0) (hscale : scale ≠ 0)
    (f : BlockVec M N → ℝ) :
    scaledFunction amp⁻¹ scale⁻¹ (scaledFunction amp scale f) = f := by
  funext x
  unfold scaledFunction scaleVec
  have hsimp : (fun m j => scale * (scale⁻¹ * x m j)) = x := by
    funext m j
    field_simp
  rw [show (scale⁻¹ • x : BlockVec M N) =
      fun m j => scale⁻¹ * x m j by rfl]
  change amp⁻¹ * (amp * f (fun m j => scale * (scale⁻¹ * x m j))) = f x
  rw [hsimp]
  field_simp

/-- Exact two-sided covariance for a named base subgradient. -/
theorem qSubgradient_scaled_iff {M N : Nat} {c amp scale : ℝ}
    (hamp : 0 < amp) (hscale : scale ≠ 0)
    {f : BlockVec M N → ℝ} (x g : BlockVec M N) :
    QSubgradient (amp * c * scale ^ 2) (scaledFunction amp scale f) x
        ((amp * scale) • g) ↔
      QSubgradient c f (scaleVec scale x) g := by
  constructor
  · intro hg
    have hx : x = scaleVec scale⁻¹ (scaleVec scale x) := by
      ext m j
      simp [scaleVec]
      field_simp
    have hback := qSubgradient_scaled
      (c := amp * c * scale ^ 2)
      (amp := amp⁻¹) (scale := scale⁻¹)
      (f := scaledFunction amp scale f)
      (z := x) (g := (amp * scale) • g)
      (inv_nonneg.2 hamp.le) hg (scaleVec scale x) hx
    have hcoef : amp⁻¹ * (amp * c * scale ^ 2) * (scale⁻¹) ^ 2 = c := by
      field_simp
    have hgrad : (amp⁻¹ * scale⁻¹) • ((amp * scale) • g) = g := by
      ext m j
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hcoef, scaledFunction_cancel hamp.ne' hscale, hgrad] at hback
    exact hback
  · intro hg
    exact qSubgradient_scaled hamp.le hg x rfl

/-- The literal paper coefficients transport `1`-weak convexity to
`rho`-weak convexity. -/
theorem weaklyConvex_paper_scaled {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (hf : WeaklyConvex 1 f) :
    WeaklyConvex rho (scaledFunction (G ^ 2 / rho) (rho / G) f) := by
  have hgeneric := weaklyConvex_scaled
    (rho := (1 : ℝ)) (amp := G ^ 2 / rho) (scale := rho / G)
    (by positivity) hf
  have hcoeff := (paper_scaling_coefficients hG.ne' hrho.ne').2
  norm_num at hgeneric
  rw [hcoeff] at hgeneric
  exact hgeneric

/-- At the paper coefficients, the complete quadratic-support reply is
carried by `g ↦ G g`; the equivalence, rather than only the forward
inclusion, is what a full-set oracle simulation requires. -/
theorem qSubgradient_paper_scaled_iff {M N : Nat} {G rho : ℝ}
    (hG : 0 < G) (hrho : 0 < rho)
    {f : BlockVec M N → ℝ} (x g : BlockVec M N) :
    QSubgradient (rho / 2)
        (scaledFunction (G ^ 2 / rho) (rho / G) f) x (G • g) ↔
      QSubgradient (1 / 2) f (scaleVec (rho / G) x) g := by
  have hiff := qSubgradient_scaled_iff
    (c := (1 / 2 : ℝ)) (amp := G ^ 2 / rho) (scale := rho / G)
    (by positivity) (div_ne_zero hrho.ne' hG.ne') (f := f) x g
  have hcoef : (G ^ 2 / rho) * (1 / 2 : ℝ) * (rho / G) ^ 2 = rho / 2 := by
    field_simp
  have hgrad : ((G ^ 2 / rho) * (rho / G)) • g = G • g := by
    rw [(paper_scaling_coefficients hG.ne' hrho.ne').1]
  rw [hcoef, hgrad] at hiff
  exact hiff

end

end WeaklyConvexLowerBound

