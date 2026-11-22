import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompEqActual

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

theorem globalThetaPositivePacket_det_rescale_comp_eq (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      packetDet (rescalePacket (c2 * c1) (mul_pos hc2 hc1)
        (globalThetaPositivePacket I A C C3)) := by
  rw [packetDet_rescale,
    globalThetaPositivePacket_det_rescale,
    globalThetaPositivePacket_det_rescale,
    ← mul_assoc, ← mul_pow]

theorem globalThetaPositivePacket_logVolume_rescale_comp_eq (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      packetLogVolume (rescalePacket (c2 * c1) (mul_pos hc2 hc1)
        (globalThetaPositivePacket I A C C3)) := by
  calc
    packetLogVolume (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
        (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
          packetLogVolume (rescalePacket c1 hc1
            (globalThetaPositivePacket I A C C3)) := by
      rw [packetLogVolume_rescale]
    _ = (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
          ((Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
            packetLogVolume (globalThetaPositivePacket I A C C3)) := by
      rw [globalThetaPositivePacket_logVolume_rescale]
    _ = (Fintype.card (SignedLabel l.value) : Real) * Real.log (c2 * c1) +
          packetLogVolume (globalThetaPositivePacket I A C C3) := by
      rw [Real.log_mul (ne_of_gt hc2) (ne_of_gt hc1)]
      ring
    _ = packetLogVolume (rescalePacket (c2 * c1) (mul_pos hc2 hc1)
          (globalThetaPositivePacket I A C C3)) := by
      rw [globalThetaPositivePacket_logVolume_rescale]

#check globalThetaPositivePacket_det_rescale_comp_eq
#check globalThetaPositivePacket_logVolume_rescale_comp_eq

end LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompEqActual

end