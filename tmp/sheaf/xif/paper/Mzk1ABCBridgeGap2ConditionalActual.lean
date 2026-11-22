/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual

/-! # A603: Gap 2 conditional reduction (SNamed -> real bound) + axiom gate -/

noncomputable section

namespace LeanFormal.IUT.Objects.ABCBridgeGap2Conditional

open LeanFormal.IUT.Objects.ABCBridgeGap2

/-- Conditional reduction of the Gap-2 named estimate: if the analytic estimate holds
(`SNamed`), and the RHS constant expression is nonnegative, then the paper's real-form
bound `regionVolume.toReal <= (1+eps)*weight + theta + D` holds.  This is the exact
reduction consumed by `Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight`
once the ENNReal/Real conversion (A502) is applied. -/
theorem gap2_conditional_reduction {regionVolume : ENNReal} {eps weight theta D : ℝ}
    (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (hS : SNamed regionVolume eps weight theta D) :
    regionVolume.toReal ≤ (1 + eps) * weight + theta + D :=
  gap2_real_bound hR hS

/- Axiom gate: only classical axioms allowed. -/
#print axioms gap2_conditional_reduction

end LeanFormal.IUT.Objects.ABCBridgeGap2Conditional
