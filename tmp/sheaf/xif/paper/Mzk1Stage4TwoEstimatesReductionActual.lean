import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCTwoEstimatesEvidenceActual

/-! # Mzk1Stage4TwoEstimatesReductionActual (stage4 lane; unique filename)

A596 module: thin re-export / reduction interface for the two remaining ABC estimates —
the numeric evidence instantiates the abstract `Gap1`/`Gap2` interface and the combined
bound follows from `combined`.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesReductionActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesEvidenceActual

/-- The numeric Gap 1 instance for the 11a1@l=13 data. -/
theorem gap1_instance : Gap1 ((5 / 6 : Real) * Real.log 11) (2 * Real.log 11) where
  bound := gap1_bound

/-- The numeric Gap 2 instance for the 11a1@l=13 data. -/
theorem gap2_instance :
    Gap2 (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10) where
  bound := gap2_bound

/-- The reduction: the abstract combined height bound applies to the numeric data. -/
theorem reduced_combined :
    (5 / 6 : Real) * Real.log 11 <=
      (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  combined ((5 / 6 : Real) * Real.log 11) (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10)
    gap1_instance gap2_instance

/-- The reduction in existential-constant form. -/
theorem reduced_combined_exists :
    ∃ A : Real,
      (5 / 6 : Real) * Real.log 11 <= (1 + 1 / 10 : Real) * Real.log 11 + A :=
  combined_exists ((5 / 6 : Real) * Real.log 11) (2 * Real.log 11) (Real.log 11) 11 0
    (1 / 10) gap1_instance gap2_instance

#check gap1_instance
#check gap2_instance
#check reduced_combined
#check reduced_combined_exists

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesReductionActual
end
