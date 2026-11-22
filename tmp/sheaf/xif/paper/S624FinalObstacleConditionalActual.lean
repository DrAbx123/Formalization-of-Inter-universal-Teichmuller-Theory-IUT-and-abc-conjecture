import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S624FinalObstacleConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper
open MeasureTheory

universe ua uv upi umon ui uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

/-- The exact paper-source bad-q bound: the signed hull procession average is
at most the actual source bad-q absolute log. -/
def PaperSourceBadQBound : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial

/-- The concrete obstacle is exactly the paper-source bad-q bound. -/
theorem concreteSourceComparisonObstacle_iff_paperSourceBadQBound :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      PaperSourceBadQBound (I := I) P := by
  unfold ConcreteSourceComparisonObstacle concreteSourceComparison concreteQLogVolume
  unfold PaperSourceBadQBound
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  change P.procession.average ≤ -sourceQPilotSignedLog I.initial ↔
    P.procession.average ≤ sourceBadQAbsLog I.initial
  unfold sourceQPilotSignedLog
  constructor <;> intro h <;> linarith

/-- Conditional final theorem: assuming the actual source bad-q bound, the
concrete source-comparison obstacle holds. -/
theorem concreteSourceComparisonObstacle_of_paperSourceBadQBound
    (h : PaperSourceBadQBound (I := I) P) :
    ConcreteSourceComparisonObstacle (l := l) I P :=
  (concreteSourceComparisonObstacle_iff_paperSourceBadQBound I P).mpr h

/-- Membership in the signed hull ray gives the obstacle. -/
theorem concreteSourceComparisonObstacle_of_membership
    (h : concreteQLogVolume (l := l) I ∈
      hullLogVolumeRay P.signedHullLogVolume) :
    ConcreteSourceComparisonObstacle (l := l) I P :=
  (concreteSourceComparison_iff_membership (l := l) I P).mpr h

end LeanFormal.IUT.XiFPaper.S624FinalObstacleConditionalActual

end
