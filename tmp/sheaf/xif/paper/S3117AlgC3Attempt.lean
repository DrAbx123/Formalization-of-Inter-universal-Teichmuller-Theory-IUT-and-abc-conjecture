import tmp.sheaf.xif.paper.S3117NativeDonorActual
import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual
import tmp.sheaf.n8.closure.C3Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3117NativeDonorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3117AlgC3Attempt

/-- Alg-carrier C3 data: the corrected native donor structure. -/
abbrev SourcePilotRegionDataAlg (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))] : Type 1 :=
  S3117NativeSourcePilotRegionDonors X

/-- Replace theta packet by the concrete source-theater packet. -/
noncomputable def c3WithSourceTheaterThetaAlg
    (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (D : SourcePilotRegionDataAlg X) : SourcePilotRegionDataAlg X :=
  { D with thetaPacket := (sourceTheater fiveLabel).thetaPacket }

/-- Alg-carrier actual signed C3 alias. -/
noncomputable abbrev actualSignedC3Alg
    (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (D : SourcePilotRegionDataAlg X) : SourcePilotRegionDataAlg X :=
  c3WithSourceTheaterThetaAlg X D

#check SourcePilotRegionDataAlg
#check c3WithSourceTheaterThetaAlg
#check actualSignedC3Alg

end LeanFormal.IUT.XiFPaper.S3117AlgC3Attempt
end