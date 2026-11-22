import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetCompGenericActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

universe ua uv upi umon ui u_label

theorem packetDet_pos_generic_comp {label : Type u_label} [Fintype label]
    (p : PositivePacket label) : 0 < packetDet p := by
  rw [packetDet_eq_prod]
  exact Finset.prod_pos (fun i _ => p.positive i)

theorem packetDet_rescale_log_generic_comp {label : Type u_label} [Fintype label]
    (p : PositivePacket label) (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc p)) =
      (Fintype.card label : Real) * Real.log c + Real.log (packetDet p) := by
  rw [packetDet_rescale]
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hc))
    (ne_of_gt (packetDet_pos_generic_comp p))]
  rw [Real.log_pow]

theorem packetDet_rescale_log_comp_generic {label : Type u_label} [Fintype label]
    (p : PositivePacket label) (c1 c2 : Real) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    Real.log (packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1 p))) =
      (Fintype.card label : Real) * (Real.log c2 + Real.log c1) +
        Real.log (packetDet p) := by
  rw [packetDet_rescale_log_generic_comp,
    packetDet_rescale_log_generic_comp]
  ring

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_log_det_rescale_comp (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    Real.log (packetDet (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3)))) =
      (Fintype.card (SignedLabel l.value) : Real) *
        (Real.log c2 + Real.log c1) +
          Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  exact packetDet_rescale_log_comp_generic
    (globalThetaPositivePacket I A C C3) c1 c2 hc1 hc2

#check globalThetaPositivePacket_log_det_rescale_comp

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetCompGenericActual

end