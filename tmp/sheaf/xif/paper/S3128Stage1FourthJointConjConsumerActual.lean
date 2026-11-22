import tmp.sheaf.xif.paper.S1385HDDHullDetActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConjConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive}

theorem S3128Stage1FourthJoint_frozen :
    HullDeterminantLogVolumeFrozenSpec :=
  s1385FrozenSpec_actual

theorem S3128Stage1FourthJoint_conj
    {V : Type uv} [Fintype V]
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : GlobalComparisonCondition (I := I) R n) :
    HullDeterminantLogVolumeFrozenSpec ∧
      qPilotThetaHullComparison (I := I) R n :=
  ⟨s1385FrozenSpec_actual,
    qPilotThetaHullComparison_of_condition (I := I) R n h⟩

#check S3128Stage1FourthJoint_frozen
#check S3128Stage1FourthJoint_conj
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConjConsumerActual