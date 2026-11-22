import tmp.sheaf.xif.paper.KummerThetaPacketDetInverseActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInvRpowPosActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInverseActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_pos_inv :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_det_rescale_inv_rpow_pos (c : Real)
    (hc : 0 < c) :
    0 < packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) := by
  rw [globalThetaPositivePacket_det_rescale_inv]
  exact globalThetaPositivePacket_det_pos_inv I A C C3

theorem globalThetaPositivePacket_det_rescale_inv_rpow_ne_zero (c : Real)
    (hc : 0 < c) :
    packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_rescale_inv_rpow_pos I A C C3 c hc)

theorem globalThetaPositivePacket_det_rescale_inv_eq_rpow (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      (globalThetaPacket I A C C3).q ^
        (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_inv,
    globalThetaPositivePacket_det_eq_exp_gauss,
    Real.rpow_def_of_pos (globalThetaPacket I A C C3).q_pos]
  rw [mul_comm (Real.log (globalThetaPacket I A C C3).q)
    (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real))]

#check globalThetaPositivePacket_det_rescale_inv_rpow_pos
#check globalThetaPositivePacket_det_rescale_inv_rpow_ne_zero

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInvRpowPosActual

end