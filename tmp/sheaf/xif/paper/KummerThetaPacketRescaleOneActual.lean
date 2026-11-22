import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleOneActual

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

theorem globalThetaPositivePacket_rescale_one_scale_consumer
    (j : SignedLabel l.value) :
    (rescalePacket (1 : Real) zero_lt_one
      (globalThetaPositivePacket I A C C3)).scale j =
      (globalThetaPositivePacket I A C C3).scale j := by
  simp [rescalePacket]

theorem globalThetaPositivePacket_det_rescale_one :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (globalThetaPositivePacket I A C C3)) =
      packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_rescale, one_pow, one_mul]

theorem globalThetaPositivePacket_logVolume_rescale_one :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (globalThetaPositivePacket I A C C3)) =
      packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_rescale, Real.log_one]
  ring

#check globalThetaPositivePacket_det_rescale_one
#check globalThetaPositivePacket_logVolume_rescale_one

end LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleOneActual

end