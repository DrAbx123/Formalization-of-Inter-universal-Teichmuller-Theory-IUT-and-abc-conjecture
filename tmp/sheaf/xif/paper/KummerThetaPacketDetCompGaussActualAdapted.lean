import tmp.sheaf.xif.paper.KummerThetaPacketRescaleCompEqActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompGaussActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleCompEqActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescaleGaussActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_rescale_comp_eq_exp_gauss
    (c1 c2 : Real) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))) =
      Real.exp ((Fintype.card (SignedLabel l.value) : Real) *
        (Real.log c2 + Real.log c1) +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_rescale_comp_eq,
    globalThetaPositivePacket_det_rescale_eq_exp_gauss]
  congr 1
  rw [Real.log_mul (ne_of_gt hc2) (ne_of_gt hc1)]
  ring

#check globalThetaPositivePacket_det_rescale_comp_eq_exp_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetCompGaussActualAdapted

end