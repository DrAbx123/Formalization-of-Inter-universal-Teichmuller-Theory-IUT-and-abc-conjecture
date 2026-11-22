import tmp.sheaf.xif.paper.KummerThetaPacketRescaleCompEqActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleRpowPosActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompRpowPosActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompEqActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleRpowPosActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_rescale_comp_eq_rpow_pos (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      (c2 * c1) ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_rpow_gauss_pos]

theorem globalThetaPositivePacket_det_rescale_comp_rpow_pos (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    0 < packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq]
  exact globalThetaPositivePacket_det_rescale_rpow_pos I A C C3
    (c2 * c1) (mul_pos hc2 hc1)

theorem globalThetaPositivePacket_det_rescale_comp_rpow_ne_zero (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_rescale_comp_rpow_pos I A C C3
    c1 c2 hc1 hc2)

theorem globalThetaPositivePacket_det_rescale_comp_one_left_eq_rpow (c2 : Real)
    (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      c2 ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq_rpow_pos]
  simp

theorem globalThetaPositivePacket_det_rescale_comp_one_right_eq_rpow (c1 : Real)
    (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      c1 ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq_rpow_pos]
  simp

theorem globalThetaPositivePacket_det_rescale_comp_one_left_eq_rescale (c2 : Real)
    (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2
      (rescalePacket (1 : Real) zero_lt_one
        (globalThetaPositivePacket I A C C3))) =
      packetDet (rescalePacket c2 hc2
        (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq]
  simp

theorem globalThetaPositivePacket_det_rescale_comp_one_right_eq_rescale (c1 : Real)
    (hc1 : 0 < c1) :
    packetDet (rescalePacket (1 : Real) zero_lt_one
      (rescalePacket c1 hc1 (globalThetaPositivePacket I A C C3))) =
      packetDet (rescalePacket c1 hc1
        (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq]
  simp

#check globalThetaPositivePacket_det_rescale_comp_rpow_pos

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompRpowPosActual

end