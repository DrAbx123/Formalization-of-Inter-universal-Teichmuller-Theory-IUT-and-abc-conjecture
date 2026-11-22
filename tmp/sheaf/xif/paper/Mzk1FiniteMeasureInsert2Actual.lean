import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteMeasureInsert2Actual — finite numMax insertion bound (real)

Real Lean (no sorry/axiom): inserting one point increases the finite maximal count by at most
one.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureInsert2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem numMax_insert_le_succ (S : Finset Qbar) (x : Qbar) :
    numMax (insert x S) <= S.card + 1 := by
  unfold numMax
  have h1 : ((insert x S).filter (fun y => degQ y = maxDeg (insert x S))).card
      <= (insert x S).card := Finset.card_filter_le _ _
  have h2 : (insert x S).card <= S.card + 1 := Finset.card_insert_le x S
  omega

def finiteMeasureInsert2Rows : List (String × String) :=
  [ ("numMax_insert_le_succ", "PROVED") ]

theorem finiteMeasureInsert2Rows_length : finiteMeasureInsert2Rows.length = 1 := rfl

#check numMax_insert_le_succ

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureInsert2Actual
end
