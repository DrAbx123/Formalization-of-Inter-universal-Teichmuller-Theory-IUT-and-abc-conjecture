import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

/-! # Exact hull scaling formula (generic normed space) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullExactScalingFormulaShaActual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- Exact scaling of a closed ball: `c • closedBall x r = closedBall (c • x) (‖c‖ r)`. -/
theorem exact_scaling_formula (c : Real) (x : E) {r : Real} (hr : 0 ≤ r) :
    c • Metric.closedBall x r = Metric.closedBall (c • x) (‖c‖ * r) :=
  smul_closedBall c x hr

/-- Hull exact scaling (nonnegative scalar, ball at origin):
`c • closedBall 0 R = closedBall 0 (c R)`. -/
theorem exact_hull_scaling (c : Real) (hc : 0 ≤ c) {R : Real}
    (hR : 0 ≤ R) :
    c • Metric.closedBall (0 : E) R = Metric.closedBall (0 : E) (c * R) := by
  rw [exact_scaling_formula c 0 hR, smul_zero, Real.norm_of_nonneg hc]

#print axioms exact_scaling_formula
#print axioms exact_hull_scaling

end LeanFormal.IUT.XiFPaper.Mzk1HullExactScalingFormulaShaActual
