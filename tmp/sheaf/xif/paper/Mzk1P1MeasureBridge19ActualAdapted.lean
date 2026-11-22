import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge18ActualAdapted

/-! # Mzk1P1MeasureBridge19ActualAdapted — empty/union corollaries (real)

Real Lean (no sorry/axiom): degenerate P1 measure laws used in step-target estimates.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge19ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge14Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_empty_union (S : Finset (P1Point Qbar)) : maxDegP (∅ ∪ S) = maxDegP S := by
  rw [Finset.empty_union]

theorem numMaxP_empty_union (S : Finset (P1Point Qbar)) : numMaxP (∅ ∪ S) = numMaxP S := by
  rw [Finset.empty_union]

theorem maxDegP_union_empty_self (S : Finset (P1Point Qbar)) : maxDegP (S ∪ ∅) = maxDegP S := by
  rw [Finset.union_empty]

def p1MeasureBridge19Rows : List (String × String) :=
  [ ("maxDegP_empty_union", "PROVED"), ("numMaxP_empty_union", "PROVED"),
    ("maxDegP_union_empty_self", "PROVED") ]

theorem p1MeasureBridge19Rows_length : p1MeasureBridge19Rows.length = 3 := rfl

#check maxDegP_empty_union

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge19ActualAdapted
end
