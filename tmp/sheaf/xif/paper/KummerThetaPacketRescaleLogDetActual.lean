import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleLogDetActual

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

theorem globalThetaPositivePacket_rescale_logVolume_eq_log_det
    (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      Real.log (packetDet (rescalePacket c hc
        (globalThetaPositivePacket I A C C3))) :=
  packetLogVolume_eq_log_det _

theorem globalThetaPositivePacket_rescale_det_pos (c : Real) (hc : 0 < c) :
    0 < packetDet (rescalePacket c hc
      (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale]
  rw [globalThetaPositivePacket_det_eq_prod]
  exact mul_pos (pow_pos hc _)
    (Finset.prod_pos
      (fun j _ => (globalThetaPacket I A C C3).scale_pos j))

theorem globalThetaPositivePacket_rescale_det_eq_exp_logVolume
    (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      Real.exp (packetLogVolume (rescalePacket c hc
        (globalThetaPositivePacket I A C C3))) := by
  rw [← Real.exp_log
    (globalThetaPositivePacket_rescale_det_pos I A C C3 c hc)]
  congr 1
  exact (globalThetaPositivePacket_rescale_logVolume_eq_log_det I A C C3 c hc).symm

#check globalThetaPositivePacket_rescale_det_eq_exp_logVolume

end LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleLogDetActual

end