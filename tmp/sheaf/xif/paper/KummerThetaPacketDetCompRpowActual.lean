import tmp.sheaf.xif.paper.KummerThetaPacketDetInverseActual
import tmp.sheaf.xif.paper.KummerThetaPacketRescaleCompActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompRpowActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInverseActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_eq_rpow_gauss_local :
    packetDet (globalThetaPositivePacket I A C C3) =
      (globalThetaPacket I A C C3).q ^
        (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_eq_exp_gauss,
    Real.rpow_def_of_pos (globalThetaPacket I A C C3).q_pos]
  congr 1
  ring

theorem globalThetaPositivePacket_det_rescale_comp_eq_rpow (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      (c2 * c1) ^ Fintype.card (SignedLabel l.value) *
        (globalThetaPacket I A C C3).q ^
          (∑ j : SignedLabel l.value,
            ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_comp,
    globalThetaPositivePacket_det_eq_rpow_gauss_local]

theorem globalThetaPositivePacket_det_rescale_inv_eq_rpow (c : Real)
    (hc : 0 < c) :
    packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      (globalThetaPacket I A C C3).q ^
        (∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) := by
  rw [globalThetaPositivePacket_det_rescale_inv,
    globalThetaPositivePacket_det_eq_rpow_gauss_local]

#check globalThetaPositivePacket_det_rescale_comp_eq_rpow
#check globalThetaPositivePacket_det_rescale_inv_eq_rpow

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompRpowActual

end