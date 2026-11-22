/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionContributionNumericsActual
import Mathlib.Tactic

/-!
# Mzk1ProcessionArithmeticInstanceActual — concrete l=13, p=11, m=5 checks

A522 numeric instance for the Theta-pilot hull procession coefficient:
l = 13 (l* = 6), p = 11, m = 5.  We verify the exact closed forms of the
local contributions and their procession average `(l*+1)/12 * m * log p = 35/12 log 11`.

Pure real arithmetic (laichunwing Unit L), no comparison and no new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionArithmeticInstanceActual

open LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
open scoped BigOperators

/-- l = 13 has l* = 6. -/
theorem l_star_thirteen : (13 : Nat) = 2 * 6 + 1 := by norm_num

/-- The average of the local contributions at l = 13, p = 11, m = 5 is
`(7/12) * 5 * log 11 = 35/12 log 11`. -/
theorem average_thirteen :
    (1 / (6 : Real)) *
        (∑ j in Finset.range 7, processionContribution 5 13 j (11 : Real)) =
      (35 / 12) * Real.log (11 : Real) := by
  have h := processionContribution_average 5 6 (11 : Real) (by norm_num)
  have h13 : (2 * 6 + 1 : Nat) = 13 := by norm_num
  simpa [h13, mul_assoc] using h

/-- The average is positive. -/
theorem average_thirteen_pos :
    0 < (1 / (6 : Real)) *
        (∑ j in Finset.range 7, processionContribution 5 13 j (11 : Real)) := by
  rw [average_thirteen]
  positivity

/-- Individual local contribution at j = 1: `5/(26) * log 11`. -/
theorem contribution_one_thirteen :
    processionContribution 5 13 1 (11 : Real) = (5 / 26) * Real.log (11 : Real) := by
  unfold processionContribution
  norm_num
  ring

#check average_thirteen
#check average_thirteen_pos

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionArithmeticInstanceActual
end
