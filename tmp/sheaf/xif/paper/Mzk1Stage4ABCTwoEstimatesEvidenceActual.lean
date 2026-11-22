import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4ABCTwoEstimatesEvidenceActual (stage4 lane; unique filename)

A594 module: numeric evidence for the two remaining ABC comparison estimates in the
11a1@l=13 data, with height = (5/6) log 11, region volume = 2 log 11, weight = log 11,
hull = 11, D = 0, eps = 1/10.  Only inequalities are proved; no objects are changed.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesEvidenceActual

/-- Positivity of `log 11`. -/
theorem log11_pos : (0 : Real) < Real.log 11 :=
  Real.log_pos (by norm_num)

/-- `log 11 < 11` (from `log x <= x - 1`). -/
theorem log11_lt_eleven : Real.log 11 < 11 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
  linarith

/-- Gap 1 slack: `(5/6) log 11 < 2 log 11`. -/
theorem gap1_slack : (5 / 6 : Real) * Real.log 11 < 2 * Real.log 11 := by
  nlinarith [log11_pos]

/-- Gap 1: height <= region volume. -/
theorem gap1_bound : (5 / 6 : Real) * Real.log 11 <= 2 * Real.log 11 :=
  le_of_lt gap1_slack

/-- Gap 2 slack: `2 log 11 < (1 + 1/10) log 11 + 11`. -/
theorem gap2_slack :
    2 * Real.log 11 < (1 + 1 / 10 : Real) * Real.log 11 + 11 := by
  nlinarith [log11_lt_eleven]

/-- Gap 2: region volume <= (1 + eps) weight + hull + D. -/
theorem gap2_bound :
    2 * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0 :=
  le_of_lt (by linarith [gap2_slack])

/-- Combined: height <= (1 + eps) weight + hull + D. -/
theorem combined_bound :
    (5 / 6 : Real) * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0 :=
  le_trans (le_of_lt gap1_slack) gap2_bound

#check log11_pos
#check log11_lt_eleven
#check gap1_slack
#check gap1_bound
#check gap2_slack
#check gap2_bound
#check combined_bound

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesEvidenceActual
end
