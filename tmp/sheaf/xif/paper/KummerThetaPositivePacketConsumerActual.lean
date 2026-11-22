import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

abbrev globalThetaPacket : FiniteThetaPacket l :=
  (globalKummerIndActionsData I A C C3).globalThetaPacket

abbrev globalThetaPositivePacket : PositivePacket (SignedLabel l.value) :=
  FiniteThetaPacket.toPositivePacket (globalThetaPacket I A C C3)

theorem globalThetaPositivePacket_scale (j : SignedLabel l.value) :
    (globalThetaPositivePacket I A C C3).scale j =
      (globalThetaPacket I A C C3).scale j := rfl

theorem globalThetaPositivePacket_positive (j : SignedLabel l.value) :
    0 < (globalThetaPositivePacket I A C C3).scale j := by
  rw [globalThetaPositivePacket_scale]
  exact (globalThetaPacket I A C C3).scale_pos j

theorem globalThetaPositivePacket_det_eq_prod :
    packetDet (globalThetaPositivePacket I A C C3) =
      ∏ j : SignedLabel l.value, (globalThetaPacket I A C C3).scale j := by
  exact FiniteThetaPacket.toPositivePacket_det_eq_prod (globalThetaPacket I A C C3)

theorem globalThetaPositivePacket_logVolume_eq_sum :
    packetLogVolume (globalThetaPositivePacket I A C C3) =
      ∑ j : SignedLabel l.value, Real.log ((globalThetaPacket I A C C3).scale j) := by
  exact FiniteThetaPacket.toPositivePacket_logVolume_eq_sum (globalThetaPacket I A C C3)

theorem globalThetaPositivePacket_logVolume_eq_log_det :
    packetLogVolume (globalThetaPositivePacket I A C C3) =
      Real.log (packetDet (globalThetaPositivePacket I A C C3)) := by
  exact FiniteThetaPacket.toPositivePacket_logVolume_eq_log_det (globalThetaPacket I A C C3)

theorem globalThetaPositivePacket_neg_invariant :
    (∑ j : SignedLabel l.value,
        Real.log ((globalThetaPositivePacket I A C C3).scale (SignedLabel.neg j))) =
      packetLogVolume (globalThetaPositivePacket I A C C3) := by
  exact FiniteThetaPacket.toPositivePacket_neg_invariant (globalThetaPacket I A C C3)

theorem globalThetaPositivePacket_det_rescale (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      c ^ Fintype.card (SignedLabel l.value) *
        packetDet (globalThetaPositivePacket I A C C3) :=
  FiniteThetaPacket.toPositivePacket_det_rescale
    (globalThetaPacket I A C C3) c hc

theorem globalThetaPositivePacket_logVolume_rescale (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc (globalThetaPositivePacket I A C C3)) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        packetLogVolume (globalThetaPositivePacket I A C C3) :=
  FiniteThetaPacket.toPositivePacket_logVolume_rescale
    (globalThetaPacket I A C C3) c hc

#check globalThetaPositivePacket_logVolume_eq_sum
#check globalThetaPositivePacket_logVolume_eq_log_det

end LeanFormal.IUT.XiFPaper.KummerThetaPositivePacketConsumerActual

end