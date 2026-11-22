import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDeterminantConsumerActual

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

theorem globalThetaPositivePacket_det_pos :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_det_ne_zero :
    packetDet (globalThetaPositivePacket I A C C3) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_pos I A C C3)

theorem globalThetaPositivePacket_log_det_eq_logVolume :
    Real.log (packetDet (globalThetaPositivePacket I A C C3)) =
      packetLogVolume (globalThetaPositivePacket I A C C3) :=
  (globalThetaPositivePacket_logVolume_eq_log_det I A C C3).symm

theorem globalThetaPositivePacket_log_det_eq_sum :
    Real.log (packetDet (globalThetaPositivePacket I A C C3)) =
      ∑ j : SignedLabel l.value,
        Real.log ((globalThetaPacket I A C C3).scale j) := by
  rw [globalThetaPositivePacket_log_det_eq_logVolume,
    globalThetaPositivePacket_logVolume_eq_sum]

#check globalThetaPositivePacket_det_pos
#check globalThetaPositivePacket_log_det_eq_sum

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDeterminantConsumerActual

end