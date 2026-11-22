import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.ConcreteSourceComparisonInequalityActual
import tmp.sheaf.xif.paper.ConcreteSourceQIdentificationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S621ConcreteComparisonTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual

universe ua upi umon ui uX uLabel

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

/-- Target reduction: the concrete obstacle is exactly the bad-q absolute-log
bound on the signed hull average. -/
theorem concreteSourceComparisonObstacle_iff_badQAbsLog :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial := by
  unfold ConcreteSourceComparisonObstacle concreteSourceComparison concreteQLogVolume
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  rw [sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-- Exact minimal gap: the bad-q absolute-log bound on the signed hull
average. -/
def ConcreteSourceComparisonMinimalGap : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial

theorem concreteSourceComparisonObstacle_iff_minimalGap :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      ConcreteSourceComparisonMinimalGap (l := l) I P :=
  concreteSourceComparisonObstacle_iff_badQAbsLog (l := l) I P

/-- Exact refutation: zero source bad-q absolute log and positive signed hull
average make the target false. -/
theorem not_concreteSourceComparisonObstacle_of_badQAbsLog_zero
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    ¬ ConcreteSourceComparisonObstacle (l := l) I P := by
  intro h
  have hbound := (concreteSourceComparisonObstacle_iff_badQAbsLog
    (l := l) I P).mp h
  linarith

end LeanFormal.IUT.XiFPaper.S621ConcreteComparisonTargetActual

end
