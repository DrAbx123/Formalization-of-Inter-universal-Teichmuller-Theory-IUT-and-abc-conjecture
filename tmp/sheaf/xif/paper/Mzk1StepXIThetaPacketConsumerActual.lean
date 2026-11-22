import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge

/-!
# Mzk1StepXIThetaPacketConsumerActual — consumer theorems over the StepXI theta-packet
bridge (tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIThetaPacketConsumerActual

open LeanFormal.IUT
open scoped BigOperators

/-- Consumer: the positive packet scales are positive. -/
theorem consumer_positive {l : PrimeGeFive} (packet : FiniteThetaPacket l)
    (j : SignedLabel l.value) : 0 < packet.toPositivePacket.scale j :=
  FiniteThetaPacket.toPositivePacket_positive packet j

/-- Consumer: positive packet log-volume equals the sum of the log-scales. -/
theorem consumer_logVolume_eq_sum {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    packetLogVolume packet.toPositivePacket =
      ∑ j : SignedLabel l.value, Real.log (packet.scale j) :=
  FiniteThetaPacket.toPositivePacket_logVolume_eq_sum packet

/-- Consumer: positive packet log-volume equals log of the determinant. -/
theorem consumer_logVolume_eq_log_det {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    packetLogVolume packet.toPositivePacket =
      Real.log (packetDet packet.toPositivePacket) :=
  FiniteThetaPacket.toPositivePacket_logVolume_eq_log_det packet

/-- Consumer: the log-volume is invariant under the signed-label negation. -/
theorem consumer_neg_invariant {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    (∑ j : SignedLabel l.value,
        Real.log (packet.toPositivePacket.scale (SignedLabel.neg j))) =
      packetLogVolume packet.toPositivePacket :=
  FiniteThetaPacket.toPositivePacket_neg_invariant packet

#check consumer_positive
#check consumer_logVolume_eq_sum
#check consumer_logVolume_eq_log_det
#check consumer_neg_invariant

end LeanFormal.IUT.XiFPaper.Mzk1StepXIThetaPacketConsumerActual
end
