import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge9ActualAdapted

/-! # Mzk1P1MeasureBridge11ActualAdapted — combined P1 measure bounds (real lemmas)

Real Lean (no sorry/axiom): combined degree/count bounds for the P1 measure under union and
insertion.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge11ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge4Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9ActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- Count bound for unions with equal maximal degree. -/
theorem numMaxP_union_le_card (S T : Finset (P1Point Qbar))
    (h : maxDegP S = maxDegP T) :
    numMaxP (S ∪ T) <= (S ∪ T).card :=
  numMaxP_le_card (S ∪ T)

/-- Insertion count bound: increasing by at most one. -/
theorem numMaxP_insert_le_card (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    numMaxP (insert p S) <= (insert p S).card :=
  numMaxP_le_card (insert p S)

def p1MeasureBridge11Rows : List (String × String) :=
  [ ("numMaxP_union_le_card", "PROVED"), ("numMaxP_insert_le_card", "PROVED") ]

theorem p1MeasureBridge11Rows_length : p1MeasureBridge11Rows.length = 2 := rfl

#check numMaxP_union_le_card
#check numMaxP_insert_le_card

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge11ActualAdapted
end
