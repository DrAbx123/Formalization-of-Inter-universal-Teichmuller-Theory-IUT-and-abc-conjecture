import tmp.sheaf.xif.paper.S1585UnitBallPositiveFiniteActual

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1586CompletionProperActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1585UnitBallPositiveFiniteActual

/-- Exact first missing instance field: every closed ball in the canonical
completion is compact. This is exactly the field of ProperSpace. -/
def S1586ClosedBallCompact (P : NumberField.FinitePlace ℚ) : Prop :=
  ∀ (x : Completion P) (r : Real), IsCompact (Metric.closedBall x r)

/-- Closed-ball compactness is exactly the properness condition. -/
theorem s1586ProperSpace_of_closedBallCompact
    (P : NumberField.FinitePlace ℚ) (h : S1586ClosedBallCompact P) :
    ProperSpace (Completion P) :=
  ProperSpace.mk h

/-- The same condition as a properness statement. -/
theorem s1586ClosedBallCompact_iff_properSpace
    (P : NumberField.FinitePlace ℚ) :
    S1586ClosedBallCompact P ↔ ProperSpace (Completion P) := by
  constructor
  · exact s1586ProperSpace_of_closedBallCompact P
  · intro h
    exact ProperSpace.isCompact_closedBall

end LeanFormal.IUT.XiFPaper.S1586CompletionProperActual

end
