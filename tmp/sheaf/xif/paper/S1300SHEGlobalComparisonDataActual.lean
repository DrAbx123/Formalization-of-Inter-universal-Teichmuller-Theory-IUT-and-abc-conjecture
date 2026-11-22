import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEGlobalComparisonDataActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

structure S1300SHEGlobalComparisonData : Type where
  condition : Prop
  comparison : Prop
  iff : condition ↔ comparison
  condition_eq : condition = GlobalComparisonCondition (I := I) R n
  comparison_eq : comparison = qPilotThetaHullComparison (I := I) R n

noncomputable def S1300SHEGlobalComparisonData.of :
    S1300SHEGlobalComparisonData (I := I) R n where
  condition := GlobalComparisonCondition (I := I) R n
  comparison := qPilotThetaHullComparison (I := I) R n
  iff := GlobalComparisonCondition_iff (I := I) R n
  condition_eq := rfl
  comparison_eq := rfl

#check S1300SHEGlobalComparisonData
#check S1300SHEGlobalComparisonData.of
end LeanFormal.IUT.XiFPaper.S1300SHEGlobalComparisonDataActual
end
