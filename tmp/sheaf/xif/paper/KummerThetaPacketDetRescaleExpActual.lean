import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleExpActual

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

theorem globalThetaPositivePacket_det_pos_local :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_log_det_rescale_local (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  rw [← packetLogVolume_eq_log_det
    (rescalePacket c hc (globalThetaPositivePacket I A C C3))]
  rw [globalThetaPositivePacket_logVolume_rescale]
  rw [packetLogVolume_eq_log_det]

theorem globalThetaPositivePacket_det_rescale_pos_local (c : Real) (hc : 0 < c) :
    0 < packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale]
  exact mul_pos (pow_pos hc _)
    (globalThetaPositivePacket_det_pos_local I A C C3)

theorem globalThetaPositivePacket_det_rescale_eq_exp (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        Real.log (packetDet (globalThetaPositivePacket I A C C3))) := by
  rw [← Real.exp_log
    (globalThetaPositivePacket_det_rescale_pos_local I A C C3 c hc)]
  rw [globalThetaPositivePacket_log_det_rescale_local]

#check globalThetaPositivePacket_det_rescale_eq_exp

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleExpActual

end