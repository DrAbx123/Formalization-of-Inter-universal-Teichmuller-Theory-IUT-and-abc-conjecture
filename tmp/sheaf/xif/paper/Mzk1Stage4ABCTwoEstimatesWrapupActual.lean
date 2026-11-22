import tmp.sheaf.xif.paper.Mzk1Stage4ABCTwoEstimatesEvidenceActual

/-! # Mzk1Stage4ABCTwoEstimatesWrapupActual (stage4 lane; unique filename)

A594 module: wrap-up of the two remaining ABC estimates as one numeric evidence record
for the 11a1@l=13 data.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesWrapupActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesEvidenceActual

/-- Numeric record for the two remaining ABC comparison estimates. -/
structure TwoEstimatesNumeric where
  /-- Positivity of the log height coordinate. -/
  log_pos : (0 : Real) < Real.log 11
  /-- Gap 1 (height vs region volume). -/
  gap1 : (5 / 6 : Real) * Real.log 11 <= 2 * Real.log 11
  /-- Gap 2 (region-volume estimate). -/
  gap2 : 2 * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0
  /-- The combined height bound. -/
  combined : (5 / 6 : Real) * Real.log 11 <=
    (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0

/-- Construct the numeric record from the evidence lemmas. -/
noncomputable def twoEstimatesNumeric : TwoEstimatesNumeric where
  log_pos := log11_pos
  gap1 := gap1_bound
  gap2 := gap2_bound
  combined := combined_bound

/-- Consumer: the recorded Gap 1. -/
theorem twoEstimates_gap1 :
    (5 / 6 : Real) * Real.log 11 <= 2 * Real.log 11 :=
  twoEstimatesNumeric.gap1

/-- Consumer: the recorded Gap 2. -/
theorem twoEstimates_gap2 :
    2 * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0 :=
  twoEstimatesNumeric.gap2

/-- Consumer: the recorded combined bound. -/
theorem twoEstimates_combined :
    (5 / 6 : Real) * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0 :=
  twoEstimatesNumeric.combined

#check TwoEstimatesNumeric
#check twoEstimatesNumeric
#check twoEstimates_gap1
#check twoEstimates_gap2
#check twoEstimates_combined

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesWrapupActual
end
