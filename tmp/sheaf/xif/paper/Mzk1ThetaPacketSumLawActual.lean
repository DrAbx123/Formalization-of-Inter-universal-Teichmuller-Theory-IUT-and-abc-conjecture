import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge

/-!
# Mzk1ThetaPacketSumLawActual — derived finite-sum laws for the StepXI positive theta packet
(new theorems from the existing ThetaPacketBridge asset; no copies/bookkeeping).
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPacketSumLawActual

open LeanFormal.IUT
open scoped BigOperators

/-- Derived: the log-volume is the sum of the logs of the positive scales. -/
theorem logVolume_eq_sum_scales {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    packetLogVolume packet.toPositivePacket =
      ∑ j : SignedLabel l.value, Real.log (packet.toPositivePacket.scale j) := by
  rw [FiniteThetaPacket.toPositivePacket_logVolume_eq_sum]
  simp

/-- Derived: the log-volume is also the negated-sum over negated labels. -/
theorem logVolume_eq_sum_neg_scales {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    packetLogVolume packet.toPositivePacket =
      ∑ j : SignedLabel l.value,
        Real.log (packet.toPositivePacket.scale (SignedLabel.neg j)) :=
  (FiniteThetaPacket.toPositivePacket_neg_invariant packet).symm

/-- Derived: the two label sums agree. -/
theorem sum_scales_eq_sum_neg_scales {l : PrimeGeFive} (packet : FiniteThetaPacket l) :
    (∑ j : SignedLabel l.value, Real.log (packet.toPositivePacket.scale j)) =
      ∑ j : SignedLabel l.value,
        Real.log (packet.toPositivePacket.scale (SignedLabel.neg j)) := by
  rw [← logVolume_eq_sum_scales, logVolume_eq_sum_neg_scales]

#check logVolume_eq_sum_scales
#check logVolume_eq_sum_neg_scales
#check sum_scales_eq_sum_neg_scales

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPacketSumLawActual
end
