import tmp.sheaf.xif.paper.KummerThetaPacketLogDetFormulaActual
import tmp.sheaf.xif.paper.KummerThetaPacketLogDetRescaleActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetFormulaActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetRescaleActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_log_det_eq_gauss_mul_log_q_consumer :
    Real.log (packetDet (globalThetaPositivePacket I A C C3)) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
        Real.log (globalThetaPacket I A C C3).q :=
  globalThetaPositivePacket_log_det_eq_gauss_mul_log_q I A C C3

theorem globalThetaPositivePacket_log_det_rescale_eq_gauss (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc
      (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [globalThetaPositivePacket_log_det_rescale,
    globalThetaPositivePacket_log_det_eq_gauss_mul_log_q_consumer]

#check globalThetaPositivePacket_log_det_rescale_eq_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

end