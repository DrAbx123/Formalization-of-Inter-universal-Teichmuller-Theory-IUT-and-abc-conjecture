import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge17ActualAdapted

/-! # Mzk1P1MeasureBridge18ActualAdapted — insert-infinity degree law (real)

Real Lean (no sorry/axiom): adding the point at infinity gives P1 maximal degree
max 1 (maxDegP ·).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge18ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

/-- Inserting infinity into an arbitrary P1 set raises the maximal degree to at least 1. -/
theorem maxDegP_insert_infty (S : Finset (P1Point Qbar)) :
    maxDegP (insert P1Point.infty S) = max 1 (maxDegP S) := by
  unfold maxDegP
  rw [Finset.sup_insert]
  rfl

def p1MeasureBridge18Rows : List (String × String) :=
  [ ("maxDegP_insert_infty", "PROVED") ]

theorem p1MeasureBridge18Rows_length : p1MeasureBridge18Rows.length = 1 := rfl

#check maxDegP_insert_infty

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge18ActualAdapted
end
