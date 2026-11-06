import WC.Moreau

/-! Exact scalar/spatial transport of the actual Moreau gradient. -/

noncomputable section
namespace WC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem scaled_moreau_gradient {a b G ρ : ℝ} {f : E → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hG : 0 ≤ G) (hρ : 0 < ρ)
    (hlip : GloballyLipschitz G f) (hwc : WeaklyConvex ρ f) (x : E) :
    gradient (moreauEnvelope (1 / (2 * (a * b ^ 2 * ρ))) (scaleFunction a b f)) x =
      (a * b) • gradient (moreauEnvelope (1 / (2 * ρ)) f) (b • x) := by
  let F := scaleFunction a b f
  let s := a * b ^ 2 * ρ
  have hs : 0 < s := by dsimp [s]; positivity
  have hFLip : GloballyLipschitz (a * b * G) F := lipschitz_scale ha.le hb.le hlip
  have hFWC : WeaklyConvex s F := weaklyConvex_scale ha.le hb.le hwc
  have hFG : 0 ≤ a * b * G := by positivity
  let p := proximalPoint s F x
  have hp := proximalPoint_spec hs hFG hFLip x
  have ht : IsProxPoint (1 / (2 * ρ)) f (b • x) (b • p) := by
    have hq : IsQuadraticMinimizer s F x p := by
      intro y
      simpa only [proxObjective_eq_quadratic hs.ne'] using hp y
    have hbase := (quadraticMinimizer_scale_iff (μ := ρ) ha hb).mp hq
    intro y
    simpa only [proxObjective_eq_quadratic hρ.ne'] using hbase y
  have heq : b • p = proximalPoint ρ f (b • x) :=
    ht.unique hρ hwc (proximalPoint_spec hρ hG hlip (b • x))
  rw [moreau_gradient_eq hs hFG hFLip hFWC,
    moreau_gradient_eq hρ hG hlip hwc, ← heq, ← smul_sub, smul_smul, smul_smul]
  change (2 * s) • (x - p) = ((a * b) * (2 * ρ) * b) • (x - p)
  congr 1
  dsimp [s]
  ring

end WC
