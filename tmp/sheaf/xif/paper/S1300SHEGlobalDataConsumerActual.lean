import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEGlobalDataConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Consumer of actual global comparison data: the exact source condition
is equivalent to the inequality between the data's hull log-volume and
q-pilot magnitude fields. -/
theorem S1300SHE_globalData_condition_iff :
    GlobalComparisonCondition (I := I) R n ↔
      (globalHullQPilotComparisonData (I := I) R n).hullLogVolume <=
        (globalHullQPilotComparisonData (I := I) R n).qPilotMagnitude := by
  unfold GlobalComparisonCondition
  constructor <;> intro h <;> simpa [globalHullQPilotComparisonData] using h

#check S1300SHE_globalData_condition_iff
end LeanFormal.IUT.XiFPaper.S1300SHEGlobalDataConsumerActual
end
