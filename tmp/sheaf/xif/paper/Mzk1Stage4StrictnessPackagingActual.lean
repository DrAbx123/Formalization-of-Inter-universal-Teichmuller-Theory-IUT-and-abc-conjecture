import tmp.sheaf.xif.paper.Mzk1Stage4OneDimStrictnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4ProductStrictnessActual

/-! # Mzk1Stage4StrictnessPackagingActual (stage4 lane; unique filename)

A581 module: packaging of the 1D smooth (open/closed ball) strictness and the product
strictness into one report usable by the strict_measure / scaling chain.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictnessPackagingActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessActual

/-- The strictness report: 1D interval/ball strictness plus product strictness. -/
structure StrictnessReport where
  /-- Half open interval has strictly smaller volume. -/
  interval_strict : ∀ r : Real, 0 < r →
    volume (Set.Ioo (-(r / 2)) (r / 2)) < volume (Set.Ioo (-r) r)
  /-- Half open ball has strictly smaller volume. -/
  ball_strict : ∀ r : Real, 0 < r →
    volume (Metric.ball (0 : Real) (r / 2)) < volume (Metric.ball (0 : Real) r)
  /-- Half closed ball has strictly smaller volume. -/
  closedBall_strict : ∀ r : Real, 0 < r →
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r)
  /-- Product strictness for positive two-factor products. -/
  product_strict : ∀ {a b c d : Real}, 0 < a → 0 < b → a < c → b < d →
    a * b < c * d

/-- Construct the strictness report from the green strictness lemmas. -/
noncomputable def strictnessReport : StrictnessReport where
  interval_strict := fun r hr => volume_half_interval_lt hr
  ball_strict := fun r hr => volume_ball_half_lt hr
  closedBall_strict := fun r hr => volume_closedBall_half_lt hr
  product_strict := fun ha hb hac hbd => mul_strict_both_pos ha hb hac hbd

/-- Consumer: the report's closed-ball strictness. -/
theorem report_closedBall {r : Real} (hr : 0 < r) :
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r) :=
  strictnessReport.closedBall_strict r hr

/-- Consumer: the report's product strictness. -/
theorem report_product {a b c d : Real} (ha : 0 < a) (hb : 0 < b)
    (hac : a < c) (hbd : b < d) : a * b < c * d :=
  strictnessReport.product_strict ha hb hac hbd

#check StrictnessReport
#check strictnessReport
#check report_closedBall
#check report_product

end LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictnessPackagingActual
end
