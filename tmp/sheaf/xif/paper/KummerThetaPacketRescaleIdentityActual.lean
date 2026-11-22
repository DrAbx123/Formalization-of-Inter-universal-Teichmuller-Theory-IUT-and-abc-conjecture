import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleIdentityActual

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

theorem globalThetaPositivePacket_rescale_comp_scale (c1 c2 : Real)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (j : SignedLabel l.value) :
    (rescalePacket c2 hc2 (rescalePacket c1 hc1
      (globalThetaPositivePacket I A C C3))).scale j =
      (rescalePacket (c2 * c1) (mul_pos hc2 hc1)
        (globalThetaPositivePacket I A C C3)).scale j := by
  simp [rescalePacket]
  ring

theorem globalThetaPositivePacket_rescale_inv_scale (c : Real) (hc : 0 < c)
    (j : SignedLabel l.value) :
    (rescalePacket (1 / c) (one_div_pos.mpr hc)
      (rescalePacket c hc (globalThetaPositivePacket I A C C3))).scale j =
      (globalThetaPositivePacket I A C C3).scale j := by
  simp [rescalePacket]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

#check globalThetaPositivePacket_rescale_comp_scale
#check globalThetaPositivePacket_rescale_inv_scale

end LeanFormal.IUT.XiFPaper.KummerThetaPacketRescaleIdentityActual

end