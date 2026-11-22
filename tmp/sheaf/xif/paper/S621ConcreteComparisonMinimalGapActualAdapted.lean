import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.ConcreteSourceComparisonInequalityActualAdapted

-- S621: exact minimal gap for the final target.
-- ConcreteSourceComparisonObstacle is equivalent to the source bad-q
-- absolute-log inequality; no unconditional proof is asserted.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonInequalityActualAdapted

universe ua upi umon ui uX uLabel

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

theorem obstacle_iff_badQAbsLog :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial := by
  unfold ConcreteSourceComparisonObstacle concreteSourceComparison concreteQLogVolume
  have hq : (paperQPilotObjectConcrete (l := l) I).qPilotLogVolume =
      -sourceBadQAbsLog I.initial := by
    rw [paperQPilotObjectConcrete_qPilotLogVolume]
    rfl
  rw [hq]
  constructor <;> intro h <;> linarith

/-- The exact minimal gap: the source signed-hull average is bounded by
/-- the actual bad-q absolute log sum. -/
def ConcreteSourceComparisonMinimalGap : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial

theorem obstacle_iff_minimalGap :
    ConcreteSourceComparisonObstacle (l := l) I P ↔
      ConcreteSourceComparisonMinimalGap (I := I) P := by
  unfold ConcreteSourceComparisonMinimalGap
  exact obstacle_iff_badQAbsLog (l := l) I P

theorem not_obstacle_of_zero_badQ_positive_average
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    ¬ ConcreteSourceComparisonObstacle (l := l) I P := by
  exact (obstacle_iff_minimalGap (l := l) I P).mpr
    (by simpa [hzero] using (not_le.mpr havg))

#check obstacle_iff_badQAbsLog
#check ConcreteSourceComparisonMinimalGap
#check obstacle_iff_minimalGap

end LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual

end