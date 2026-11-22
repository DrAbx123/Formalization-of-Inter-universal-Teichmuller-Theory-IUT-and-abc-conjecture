import tmp.sheaf.xif.paper.S3117AlgC3Attempt
import tmp.sheaf.xif.paper.S2725GlobalThetaHullActual
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S3117NativeDonorActual
open LeanFormal.IUT.XiFPaper.S3117AlgC3Attempt
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3117GlobalThetaHullAlgAttempt

variable (X : N8NativeInput fiveLabel)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable (D : SourcePilotRegionDataAlg X)

/-- The alg-carrier tensor block, using only q/theta/tensor/place fields. -/
abbrev S3117AlgCarrier : Type :=
  ArithmeticTensorTupleBlock D.tensorPlaces D.tensorTuple

/-- Exact target: an actual IQ hull/log-volume interface on the alg-carrier
tensor block. -/
def S3117GlobalThetaHullAlgTarget : Prop :=
  Nonempty (IQHullLogVolumeInterface (S3117AlgCarrier X D))

/-- Exact missing ingredient: a C3LogShellTensorPacket chain for the alg
carrier.  The old chain is typed on SourcePilotRegionData, not on
SourcePilotRegionDataAlg. -/
def S3117AlgTensorPacketMissing : Prop :=
  Nonempty (Σ carrier : Type, MeasurableSpace carrier)

#check S3117AlgCarrier
#check S3117GlobalThetaHullAlgTarget
#check S3117AlgTensorPacketMissing
#check @globalThetaHullInterface

end LeanFormal.IUT.XiFPaper.S3117GlobalThetaHullAlgAttempt
end