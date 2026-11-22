import tmp.sheaf.xif.paper.Mzk1Cor312SignedProjectionActual

/-! # Consumers of signed-slot projections (chain-independent) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionActual

/-- Two contracts with the same signed slots have interchangeable conclusions. -/
theorem cor312Conclusion_congr {C D : StepXIContract}
    (hq : C.qSigned = D.qSigned) (ht : C.thetaSigned = D.thetaSigned)
    (h : Cor312Conclusion C) : Cor312Conclusion D := by
  unfold Cor312Conclusion at *
  rw [← hq, ← ht]
  exact h

/-- A contract whose signed slots are bounded directly yields the conclusion. -/
theorem cor312Conclusion_of_slots {C : StepXIContract} {q theta : Real}
    (hq : C.qSigned = q) (ht : C.thetaSigned = theta) (h : q ≤ theta) :
    Cor312Conclusion C := by
  unfold Cor312Conclusion
  rw [hq, ht]
  exact h

end LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionConsumerActual
