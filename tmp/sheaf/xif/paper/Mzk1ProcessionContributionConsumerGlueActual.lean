import tmp.sheaf.xif.paper.Mzk1ProcessionContributionNumericsActual

/-! # Mzk1ProcessionContributionConsumerGlueActual — concrete procession-average values

Small glue module (no new mathematics): instantiates the Unit L procession sum identity
at the concrete curve data of the mined verification (l = 13, m = 5, p = 11) and at
small levels.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
open scoped BigOperators

/-- Unit L at l = 13 (l* = 6), m = 5, p = 11: average = (7/12) * 5 * log 11. -/
theorem processionContribution_average_l13 :
    (1 / (6 : Real)) *
        (∑ j in Finset.range (6 + 1),
          processionContribution 5 (2 * 6 + 1) j (11 : Real)) =
      (7 / 12 : Real) * 5 * Real.log (11 : Real) := by
  have h := processionContribution_average 5 6 (11 : Real) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Unit L at l = 3 (l* = 1), m = 5, p = 11: average = (1/6) * 5 * log 11. -/
theorem processionContribution_average_l3 :
    (1 / (1 : Real)) *
        (∑ j in Finset.range (1 + 1),
          processionContribution 5 (2 * 1 + 1) j (11 : Real)) =
      (1 / 6 : Real) * 5 * Real.log (11 : Real) := by
  have h := processionContribution_average 5 1 (11 : Real) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The general coefficient (l+1)/24 with l = 13 is 7/12. -/
theorem coefficient_l13 :
    (((2 * 6 + 1 : Nat) : Real) + 1) / 24 = (7 / 12 : Real) := by
  norm_num

#check processionContribution_average_l13
#check processionContribution_average_l3
#check coefficient_l13

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionConsumerGlueActual
end
