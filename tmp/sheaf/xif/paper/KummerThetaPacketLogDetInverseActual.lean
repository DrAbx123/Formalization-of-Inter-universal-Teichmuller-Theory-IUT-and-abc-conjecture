import tmp.sheaf.xif.paper.KummerThetaPacketLogDetGaussActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetInverseActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual
open LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetGaussActual

universe ua uv upi umon ui u_label

theorem packetDet_pos_generic {label : Type u_label} [Fintype label]
    (p : PositivePacket label) : 0 < packetDet p := by
  rw [packetDet_eq_prod]
  exact Finset.prod_pos (fun i _ => p.positive i)

theorem packetDet_rescale_log_generic {label : Type u_label} [Fintype label]
    (p : PositivePacket label) (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc p)) =
      (Fintype.card label : Real) * Real.log c + Real.log (packetDet p) := by
  rw [packetDet_rescale]
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hc))
    (ne_of_gt (packetDet_pos_generic p))]
  rw [Real.log_pow]

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_log_det_rescale_inv (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3)))) =
      Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  rw [packetDet_rescale_log_generic, packetDet_rescale_log_generic]
  have hlog : Real.log (1 / c) = -Real.log c := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

#check globalThetaPositivePacket_log_det_rescale_inv

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetInverseActual

end