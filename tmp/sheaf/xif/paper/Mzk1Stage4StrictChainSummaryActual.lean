import tmp.sheaf.xif.paper.Mzk1Stage4StrictnessPackagingActual
import tmp.sheaf.xif.paper.Mzk1Stage4OneDimStrictnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4ProductStrictnessActual

/-! # Mzk1Stage4StrictChainSummaryActual (stage4 lane; unique filename)

A596 module: stage4-lane summary of the strict chain (1D interval/ball strictness and
product strictness) as a single report plus direct consumers.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictChainSummaryActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictnessPackagingActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessActual

/-- The strict chain summary report. -/
noncomputable def strictChainSummary : StrictnessReport :=
  strictnessReport

/-- Summary: half open interval has strictly smaller volume. -/
theorem strictChain_interval {r : Real} (hr : 0 < r) :
    volume (Set.Ioo (-(r / 2)) (r / 2)) < volume (Set.Ioo (-r) r) :=
  strictChainSummary.interval_strict r hr

/-- Summary: half open ball has strictly smaller volume. -/
theorem strictChain_ball {r : Real} (hr : 0 < r) :
    volume (Metric.ball (0 : Real) (r / 2)) < volume (Metric.ball (0 : Real) r) :=
  strictChainSummary.ball_strict r hr

/-- Summary: half closed ball has strictly smaller volume. -/
theorem strictChain_closedBall {r : Real} (hr : 0 < r) :
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r) :=
  strictChainSummary.closedBall_strict r hr

/-- Summary: product strictness for positive two-factor products. -/
theorem strictChain_product {a b c d : Real} (ha : 0 < a) (hb : 0 < b)
    (hac : a < c) (hbd : b < d) : a * b < c * d :=
  strictChainSummary.product_strict ha hb hac hbd

#check strictChainSummary
#check strictChain_interval
#check strictChain_ball
#check strictChain_closedBall
#check strictChain_product

end LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictChainSummaryActual
end
