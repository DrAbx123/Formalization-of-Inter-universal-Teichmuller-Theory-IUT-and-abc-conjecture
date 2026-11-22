/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

/-! # Mzk1ABCTwoEstimatesCleanGateQpilotActual — clean axiom gate for the two estimates

A607 (qpilot lane): `#print axioms` gate for the two-estimates arithmetic/
absorption lemmas and the Gap-2 real-bound consumer, plus a payload structure. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesCleanGateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual.height_le_of_twoEstimates
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual.height_le_absorbed
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual.one_add_sq_le_one_add_three
#print axioms LeanFormal.IUT.Objects.ABCBridgeGap2.gap2_real_bound

/-! ### Payload -/

/-- Payload: chained two-estimates arithmetic and the Gap-2 real bound. -/
structure TwoEstimatesCleanGate where
  chain : ∀ {h v w t D eps : Real}, 0 ≤ eps → eps ≤ 1 → 0 ≤ w →
    h ≤ (1 + eps) * v → v ≤ (1 + eps) * w + t + D →
    h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D)
  gap2Real : ∀ {regionVolume : ENNReal} {eps weight theta D : Real},
    0 ≤ (1 + eps) * weight + theta + D →
    SNamed regionVolume eps weight theta D →
    regionVolume.toReal ≤ (1 + eps) * weight + theta + D

/-- The constructed clean gate payload. -/
noncomputable def twoEstimatesCleanGate : TwoEstimatesCleanGate where
  chain := fun h0 h1 hw hge1 hge2 =>
    height_le_absorbed h0 h1 hw (height_le_of_twoEstimates h0 hge1 hge2)
  gap2Real := fun hR hS => gap2_real_bound hR hS

#check twoEstimatesCleanGate

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesCleanGateQpilotActual
end
