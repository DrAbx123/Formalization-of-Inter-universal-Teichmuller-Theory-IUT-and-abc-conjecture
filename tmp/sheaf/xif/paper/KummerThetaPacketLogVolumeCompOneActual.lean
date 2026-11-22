import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual
import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeCompOneActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_logVolume_comp_one_left (c2 : Real) (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      packetLogVolume (rescalePacket c2 hc2
        (globalThetaPositivePacket I A C C3)) := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale]
  simp

theorem globalThetaPositivePacket_logVolume_comp_one_right (c1 : Real) (hc1 : 0 < c1) :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      packetLogVolume (rescalePacket c1 hc1
        (globalThetaPositivePacket I A C C3)) := by
  rw [packetLogVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale,
    globalThetaPositivePacket_logVolume_rescale]
  simp

theorem globalThetaPositivePacket_logVolume_comp_one_left_value (c2 : Real)
    (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
        packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_comp_one_left,
    globalThetaPositivePacket_logVolume_rescale]

theorem globalThetaPositivePacket_logVolume_comp_one_right_value (c1 : Real)
    (hc1 : 0 < c1) :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
        packetLogVolume (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_logVolume_comp_one_right,
    globalThetaPositivePacket_logVolume_rescale]

theorem globalThetaPositivePacket_logVolume_comp_one_left_gauss (c2 : Real)
    (hc2 : 0 < c2) :
    packetLogVolume (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c2 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_logVolume_comp_one_left_value,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]

theorem globalThetaPositivePacket_logVolume_comp_one_right_gauss (c1 : Real)
    (hc1 : 0 < c1) :
    packetLogVolume (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c1 +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_logVolume_comp_one_right_value,
    globalThetaPositivePacket_logVolume_eq_gauss_mul_log_q_consumer]

#check globalThetaPositivePacket_logVolume_comp_one_left
#check globalThetaPositivePacket_logVolume_comp_one_right

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogVolumeCompOneActual

end