import tmp.sheaf.xif.paper.KummerThetaPacketDetInverseActual
import tmp.sheaf.xif.paper.KummerThetaPacketDetRescaleGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInvGaussActual

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

theorem globalThetaPositivePacket_det_rescale_inv_eq_exp_gauss (c : Real)
    (hc : 0 < c) :
    packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      Real.exp ((∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q) := by
  rw [globalThetaPositivePacket_det_rescale_inv,
    globalThetaPositivePacket_det_eq_exp_gauss]

#check globalThetaPositivePacket_det_rescale_inv_eq_exp_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetInvGaussActual

end