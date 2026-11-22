import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleRpowPosActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_rescale_eq_rpow_gauss_pos
    (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      c ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale,
    globalThetaPositivePacket_det_eq_exp_gauss,
    Real.rpow_def_of_pos (globalThetaPacket I A C C3).q_pos]
  rw [mul_comm (Real.log (globalThetaPacket I A C C3).q)
    (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real))]

theorem globalThetaPositivePacket_det_rescale_rpow_pos (c : Real) (hc : 0 < c) :
    0 < packetDet (rescalePacket c hc
      (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale_eq_rpow_gauss_pos]
  exact mul_pos (pow_pos hc _)
    (Real.rpow_pos_of_pos (globalThetaPacket I A C C3).q_pos _)

theorem globalThetaPositivePacket_det_rescale_ne_zero_rpow (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc
      (globalThetaPositivePacket I A C C3)) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_rescale_rpow_pos I A C C3 c hc)

#check globalThetaPositivePacket_det_rescale_rpow_pos
#check globalThetaPositivePacket_det_rescale_ne_zero_rpow

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleRpowPosActual

end