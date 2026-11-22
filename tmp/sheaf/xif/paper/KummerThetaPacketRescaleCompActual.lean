import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_rescale_comp (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      (c2 * c1) ^ Fintype.card (SignedLabel l.value) *
        packetDet (globalThetaPositivePacket I A C C3) := by
  rw [packetDet_rescale, globalThetaPositivePacket_det_rescale, mul_pow]
  ring

theorem globalThetaPositivePacket_logVolume_rescale_comp (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) *
        (Real.log c2 + Real.log c1) +
          packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [packetLogVolume_rescale, globalThetaPositivePacket_logVolume_rescale]
  ring

#check globalThetaPositivePacket_det_rescale_comp
#check globalThetaPositivePacket_logVolume_rescale_comp

end LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompActual

end