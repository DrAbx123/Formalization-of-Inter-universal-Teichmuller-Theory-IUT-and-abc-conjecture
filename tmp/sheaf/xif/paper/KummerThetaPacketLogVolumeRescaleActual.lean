import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeRescaleActual

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

theorem globalThetaPositivePacket_logVolume_rescale_consumer (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        packetLogVolume (globalThetaPositivePacket I A C C3) :=
  globalThetaPositivePacket_logVolume_rescale I A C C3 c hc

theorem globalThetaPositivePacket_logVolume_rescale_eq_sum (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        ∑ j : SignedLabel l.value,
          Real.log ((globalThetaPacket I A C C3).scale j) := by
  rw [globalThetaPositivePacket_logVolume_rescale_consumer,
    globalThetaPositivePacket_logVolume_eq_sum]

theorem globalThetaPositivePacket_det_rescale_consumer (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      c ^ Fintype.card (SignedLabel l.value) *
        packetDet (globalThetaPositivePacket I A C C3) :=
  globalThetaPositivePacket_det_rescale I A C C3 c hc

#check globalThetaPositivePacket_logVolume_rescale_eq_sum
#check globalThetaPositivePacket_det_rescale_consumer

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeRescaleActual

end