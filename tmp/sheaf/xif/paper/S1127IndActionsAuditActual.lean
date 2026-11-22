import tmp.sheaf.xif.paper.S940Ind3ImageActual
import tmp.sheaf.xif.paper.S937IndImageActual
import tmp.sheaf.xif.paper.S951ActualIndImageTransferActual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

/-! # S1127: Ind1/Ind2/Ind3 carrier and qVFamBlock transport audit

Audit only; no new action or transport object.

Actual carriers:
* Ind1: reindexed tensor packet (dependent PiTensorProduct) acted on by
  PrcAutomorphismTensorAction; source is ActualTensorPacket.
* Ind2: SourceProcessionCapsuleContract.tensorPacket, self-action ind2TensorEquiv.
* Ind3: ActualInd3Stage = TimesMuQuotient ((fPrimeStripAt 1 m).Mon v)^x,
  acted on by actualInd3StageAction; stageComparison to m=0.

qVFamBlock transport: S940 supplies only a structure with a bare map and a
nonempty base; S951 ActualIndImageTransfer requires toBlock1/2/3, the three
image equality fields and the actuality Props.  No inhabitant is asserted.
`actualIndImageDataOfTransfer` turns a supplied transfer into S928 data. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1127IndActionsAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.S937IndImageActual
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual
open LeanFormal.IUT.XiFPaper.S951ActualIndImageTransferActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

#check PrcAutomorphismTensorAction
#check ind2TensorEquiv
#check actualInd3StageAction
#check ActualInd3Stage
#check S940PacketToQVFamTransport
#check S940QVFamIndImageRequired
#check S937QVFamIndImageRequired
#check S951Ind1Carrier
#check S951Ind2Carrier
#check S951Ind3Carrier
#check ActualIndImageTransfer
#check ActualIndImageTransferRequired
#check actualIndImageDataOfTransfer
#check actualIndImageDataOfTransfer_nonempty
#check globalKummerIndActionsData
#check globalKummerIndActionsData_ind1
#check globalKummerIndActionsData_ind2
#check globalKummerIndActionsData_ind3

end LeanFormal.IUT.XiFPaper.S1127IndActionsAuditActual
end
