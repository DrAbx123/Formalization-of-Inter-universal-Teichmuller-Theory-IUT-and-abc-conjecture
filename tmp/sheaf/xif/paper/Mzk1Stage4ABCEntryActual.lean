import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCStage5InputActual

/-! # Mzk1Stage4ABCEntryActual (stage4 lane; unique filename)

A572 module: stage4-lane ABC-entry packaging — combines the numeric Theorem 1.10
height-region instance with the numeric ABC Stage 5 input into a single entry witness.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCEntryActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5InputActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual

/-- The ABC-entry witness: the numeric Stage 5 input plus the numeric Theorem 1.10
height-region inequality. -/
structure ABCEntryWitness where
  /-- ABC Stage 5 input shape (signed q/Theta comparison). -/
  stage5 : ABCStage5Input
  /-- The numeric IUT IV Theorem 1.10 inequality for 11a1 at l = 13. -/
  theorem110 : (1 / 6 : Real) * degQ11 <= theorem110RHS

/-- ABC entry is non-vacuous: the numeric instance provides a witness. -/
noncomputable def abcEntryWitness (L : Real) (hL : 0 < L) : ABCEntryWitness where
  stage5 :=
    Mzk1Stage4ABCStage5InputActual.numeric_stage5 L hL
  theorem110 :=
    theorem110_11a1_l13

/-- The ABC entry witness supplies the Stage 5 input. -/
theorem abcEntry_stage5 (W : ABCEntryWitness) : ABCStage5Input :=
  W.stage5

/-- The ABC entry witness supplies the height-region inequality. -/
theorem abcEntry_height (W : ABCEntryWitness) :
    (1 / 6 : Real) * degQ11 <= theorem110RHS :=
  W.theorem110

#check ABCEntryWitness
#check abcEntryWitness
#check abcEntry_stage5
#check abcEntry_height

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCEntryActual
end
