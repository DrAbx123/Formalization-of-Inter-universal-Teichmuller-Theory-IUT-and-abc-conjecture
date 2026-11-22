import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCEntryActual

/-! # Mzk1Stage4GapEstimatesWrapupActual (stage4 lane; unique filename)

A590 module: wrap-up linking the two formalized ABC comparison gaps to the stage4 ABC
entry witness.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapEstimatesWrapupActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCEntryActual

/-- The gap estimates supply the height bound for 11a1@l=13. -/
theorem estimates_height :
    Real.log 11 <= (1 + 1 / 10) * Real.log 11 + (11 + 0) :=
  combined (Real.log 11) (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10)
    gap1_numeric gap2_numeric

/-- The gap-estimate witness data together with the ABC entry witness. -/
structure Stage4EstimatesWitness (L : Real) (hL : 0 < L) where
  /-- The ABC entry witness (Stage 5 input + Theorem 1.10 numeric inequality). -/
  entry : ABCEntryWitness
  /-- The combined two-gap height estimate. -/
  estimate : Real.log 11 <= (1 + 1 / 10) * Real.log 11 + (11 + 0)

/-- Construct the stage4 estimates witness. -/
noncomputable def stage4EstimatesWitness (L : Real) (hL : 0 < L) :
    Stage4EstimatesWitness L hL where
  entry := abcEntryWitness L hL
  estimate := estimates_height

#check estimates_height
#check Stage4EstimatesWitness
#check stage4EstimatesWitness

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapEstimatesWrapupActual
end
