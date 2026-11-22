/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

/-! # Mzk1ABCTwoEstimatesNumericQpilotActual — numeric evidence for the two estimates

A594 (qpilot lane): explicit numeric witnesses showing the two-estimate chaining
and absorption lemmas are satisfiable with `0 < ε ≤ 1` and nonnegative weight,
plus the general conditional consumer.  No bridge object is changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

/-- Numeric evidence: concrete numbers satisfy both estimate shapes and the
chained/absorbed bounds. -/
theorem twoEstimates_numeric_witness :
    ∃ (h v w t D eps : Real), 0 < eps ∧ eps ≤ 1 ∧ 0 ≤ w ∧
      h ≤ (1 + eps) * v ∧
      v ≤ (1 + eps) * w + t + D ∧
      h ≤ (1 + eps) * ((1 + eps) * w + t + D) ∧
      h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D) := by
  refine ⟨1, 2, 2, 0, 0, 1/2, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_⟩
  · have h1 : (1 : Real) ≤ (1 + (1/2)) * 2 := by norm_num
    have h2 : (2 : Real) ≤ (1 + (1/2)) * 2 + 0 + 0 := by norm_num
    exact height_le_of_twoEstimates (by norm_num) h1 h2
  · have h1 : (1 : Real) ≤ (1 + (1/2)) * 2 := by norm_num
    have h2 : (2 : Real) ≤ (1 + (1/2)) * 2 + 0 + 0 := by norm_num
    have hchain := height_le_of_twoEstimates (by norm_num) h1 h2
    exact height_le_absorbed (by norm_num) (by norm_num) (by norm_num) hchain

/-- General consumer: the two estimates chain into the absorbed bound. -/
theorem twoEstimates_chain {h v w t D eps : Real}
    (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (hw : 0 ≤ w)
    (hge1 : h ≤ (1 + eps) * v)
    (hge2 : v ≤ (1 + eps) * w + t + D) :
    h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D) :=
  height_le_absorbed h0 h1 hw (height_le_of_twoEstimates h0 hge1 hge2)

/-- The Gap-2 named estimate as a hypothesis feeds the chain interpreter. -/
theorem gap2_named_chain {regionVolume : ENNReal} {eps weight theta D : Real}
    (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (hweight : 0 ≤ weight)
    (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (hS : SNamed regionVolume eps weight theta D)
    {h : Real} (hge1 : h ≤ (1 + eps) * regionVolume.toReal) :
    h ≤ (1 + 3 * eps) * weight + (1 + eps) * (theta + D) := by
  have hreal : regionVolume.toReal ≤ (1 + eps) * weight + theta + D :=
    gap2_real_bound hR hS
  exact twoEstimates_chain h0 h1 hweight hge1 (by linarith)

#check twoEstimates_numeric_witness
#check gap2_named_chain

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericQpilotActual
end
