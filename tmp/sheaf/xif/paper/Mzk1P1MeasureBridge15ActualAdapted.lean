import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge14ActualAdapted

/-! # Mzk1P1MeasureBridge15ActualAdapted — algebraic laws of maxDegP (real)

Real Lean (no sorry/axiom): commutativity/associativity/idempotence of the P1 maximal-degree
union law.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge15ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_union_comm (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∪ T) = maxDegP (T ∪ S) := by
  rw [maxDegP_union, maxDegP_union, max_comm]

theorem maxDegP_union_assoc (S T U : Finset (P1Point Qbar)) :
    maxDegP ((S ∪ T) ∪ U) = maxDegP (S ∪ (T ∪ U)) := by
  rw [maxDegP_union, maxDegP_union, maxDegP_union, max_assoc]

theorem maxDegP_union_self (S : Finset (P1Point Qbar)) :
    maxDegP (S ∪ S) = maxDegP S := by
  rw [Finset.union_self]

def p1MeasureBridge15Rows : List (String × String) :=
  [ ("maxDegP_union_comm", "PROVED"), ("maxDegP_union_assoc", "PROVED"),
    ("maxDegP_union_self", "PROVED") ]

theorem p1MeasureBridge15Rows_length : p1MeasureBridge15Rows.length = 3 := rfl

#check maxDegP_union_comm

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge15ActualAdapted
end
