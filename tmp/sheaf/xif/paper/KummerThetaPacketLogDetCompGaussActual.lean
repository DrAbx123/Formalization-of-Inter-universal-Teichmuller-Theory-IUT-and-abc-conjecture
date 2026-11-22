import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetCompGaussActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

universe ua uv upi umon ui u_label

theorem packetDet_pos_generic_comp_gauss {label : Type u_label} [Fintype label]
    (p : PositivePacket label) : 0 < packetDet p := by
  rw [packetDet_eq_prod]
  exact Finset.prod_pos (fun i _ => p.positive i)

theorem packetDet_rescale_log_generic_comp_gauss {label : Type u_label} [Fintype label]
    (p : PositivePacket label) (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc p)) =
      (Fintype.card label : Real) * Real.log c + Real.log (packetDet p) := by
  rw [packetDet_rescale]
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hc))
    (ne_of_gt (packetDet_pos_generic_comp_gauss p))]
  rw [Real.log_pow]

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_log_det_rescale_comp_eq_gauss
    (c1 c2 : Real) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    Real.log (packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3)))) =
      (Fintype.card (SignedLabel l.value) : Real) *
        (Real.log c2 + Real.log c1) +
        (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) *
          Real.log (globalThetaPacket I A C C3).q := by
  rw [packetDet_rescale_log_generic_comp_gauss,
    packetDet_rescale_log_generic_comp_gauss,
    globalThetaPositivePacket_log_det_eq_gauss_mul_log_q_consumer]
  ring

#check globalThetaPositivePacket_log_det_rescale_comp_eq_gauss

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetCompGaussActual

end