import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInverseActual

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

theorem globalThetaPositivePacket_det_rescale_inv (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      packetDet (globalThetaPositivePacket I A C C3) := by
  rw [packetDet_rescale, globalThetaPositivePacket_det_rescale]
  rw [← mul_assoc, ← mul_pow, one_div_mul_cancel (ne_of_gt hc), one_pow, one_mul]

theorem globalThetaPositivePacket_logVolume_rescale_inv (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [packetLogVolume_rescale, globalThetaPositivePacket_logVolume_rescale]
  have hlog : Real.log (1 / c) = -Real.log c := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

#check globalThetaPositivePacket_det_rescale_inv
#check globalThetaPositivePacket_logVolume_rescale_inv

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInverseActual

end