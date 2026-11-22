import tmp.sheaf.xif.paper.S2814SG3bLocalPacketActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2814SG3bLocalPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3101C3NativeIndexMeasureAttemptAdapted

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))
variable (C3 : SourcePilotRegionData
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

local instance s3101Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s3101Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- (a) Exact index target. -/
def S3101IndexTarget (C3 : SourcePilotRegionData
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat)) : Prop :=
  Nonempty (C3.tensorIndex ≃ Bad (nativePlaceSelection T))

/-- (b1) Packet identity. -/
def S3101PacketIdentity (C3 : SourcePilotRegionData
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat)) : Prop :=
  (haarLogVolume (actualC3LogShellTensorHaar C3)
    (actualC3LogShellTensorRegion C3)).toReal =
    ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i

/-- (b2) Per-index local Haar log bound. -/
def S3101LocalBound
    (C3 : SourcePilotRegionData
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat))
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall i : C3.tensorIndex,
    S2814LocalLogVolume C3 i <=
      nativeBadLocalWeight T (e i) * baseQLogMagnitude T (e i)

/-- Conditional assembly of the global hull bound. -/
theorem S3101_globalBound_of_components
    (hpacket : S3101PacketIdentity (C3 := C3))
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (hloc : S3101LocalBound (C3 := C3) (T := T) e) :
    (haarLogVolume (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)).toReal <=
      nativeGlobalQPilotNormalizedLogMagnitude (T := T) := by
  rw [hpacket]
  rw [nativeGlobalQPilotNormalizedLogMagnitude_eq]
  exact Finset.sum_le_sum (fun i _ => hloc i)

#check S3101IndexTarget
#check S3101PacketIdentity
#check S3101LocalBound
#check S3101_globalBound_of_components

end LeanFormal.IUT.XiFPaper.S3101C3NativeIndexMeasureAttemptAdapted
end