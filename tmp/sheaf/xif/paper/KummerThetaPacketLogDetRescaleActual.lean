import tmp.sheaf.xif.paper.KummerThetaPositivePacketConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetRescaleActual

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

theorem globalThetaPositivePacket_log_det_rescale (c : Real) (hc : 0 < c) :
    Real.log (packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3))) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  rw [← packetLogVolume_eq_log_det
    (rescalePacket c hc (globalThetaPositivePacket I A C C3))]
  rw [globalThetaPositivePacket_logVolume_rescale]
  rw [packetLogVolume_eq_log_det]

#check globalThetaPositivePacket_log_det_rescale

end LeanFormal.IUT.XiFPaper.KummerThetaPacketLogDetRescaleActual

end