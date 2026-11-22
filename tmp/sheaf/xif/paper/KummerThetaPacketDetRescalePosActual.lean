import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescalePosActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem globalThetaPositivePacket_det_eq_prod_consumer :
    packetDet (globalThetaPositivePacket I A C C3) =
      ∏ j : SignedLabel l.value, (globalThetaPacket I A C C3).scale j := by
  rw [globalThetaPositivePacket_det_eq_prod]

theorem globalThetaPositivePacket_det_pos_consumer :
    0 < packetDet (globalThetaPositivePacket I A C C3) := by
  rw [globalThetaPositivePacket_det_eq_prod_consumer]
  exact Finset.prod_pos
    (fun j _ => (globalThetaPacket I A C C3).scale_pos j)

theorem globalThetaPositivePacket_det_rescale_eq_prod (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      c ^ Fintype.card (SignedLabel l.value) *
        ∏ j : SignedLabel l.value, (globalThetaPacket I A C C3).scale j := by
  rw [globalThetaPositivePacket_det_rescale,
    globalThetaPositivePacket_det_eq_prod_consumer]

theorem globalThetaPositivePacket_det_rescale_pos (c : Real) (hc : 0 < c) :
    0 < packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) := by
  rw [globalThetaPositivePacket_det_rescale_eq_prod]
  exact mul_pos (pow_pos hc _)
    (Finset.prod_pos (fun j _ => (globalThetaPacket I A C C3).scale_pos j))

theorem globalThetaPositivePacket_det_rescale_ne_zero (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) ≠ 0 :=
  ne_of_gt (globalThetaPositivePacket_det_rescale_pos I A C C3 c hc)

theorem globalThetaPositivePacket_det_eq_prod_thetaValues :
    packetDet (globalThetaPositivePacket I A C C3) =
      ∏ j : SignedLabel l.value,
        realThetaValue (globalThetaPacket I A C C3).q j.1 := by
  rw [globalThetaPositivePacket_det_eq_prod_consumer]
  apply Finset.prod_congr rfl
  intro j _
  exact (globalThetaPacket I A C C3).scale_eq j

#check globalThetaPositivePacket_det_rescale_pos
#check globalThetaPositivePacket_det_rescale_ne_zero

end LeanFormal.IUT.XiFPaper.KummerThetaPacketDetRescalePosActual

end