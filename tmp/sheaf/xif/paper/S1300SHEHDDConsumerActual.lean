import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEHDDConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable (I : Input Label Choice)
variable {Iorig : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, Iorig.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem S1300SHEHDD_globalConsumer
    (D : S1300HDDHullDetSource I)
    (h : GlobalComparisonCondition (I := Iorig) R n) :
    (D.toS1215 (I := I)).rank = D.rank ∧
    qPilotThetaHullComparison (I := Iorig) R n :=
  ⟨rfl, qPilotThetaHullComparison_of_condition (I := Iorig) R n h⟩

#check S1300SHEHDD_globalConsumer
end LeanFormal.IUT.XiFPaper.S1300SHEHDDConsumerActual
end
