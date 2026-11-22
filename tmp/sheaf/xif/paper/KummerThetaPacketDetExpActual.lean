import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetExpActual

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

theorem globalThetaPositivePacket_det_eq_prod_local :
    packetDet (globalThetaPositivePacket I A C C3) =
      ∏ j : SignedLabel l.value, (globalThetaPacket I A C C3).scale j := by
  rw [globalThetaPositivePacket_det_eq_prod]

theorem globalThetaPositivePacket_det_pos_local :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod_local]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_exp_logVolume :
    Real.exp (packetLogVolume (globalThetaPositivePacket I A C C3)) =
      packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_eq_log_det]
  exact Real.exp_log (globalThetaPositivePacket_det_pos_local I A C C3)

theorem globalThetaPositivePacket_det_eq_exp_logVolume :
    packetDet (globalThetaPositivePacket I A C C3) =
      Real.exp (packetLogVolume (globalThetaPositivePacket I A C C3)) :=
  (globalThetaPositivePacket_exp_logVolume I A C C3).symm

#check globalThetaPositivePacket_exp_logVolume
#check globalThetaPositivePacket_det_eq_exp_logVolume

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetExpActual

end