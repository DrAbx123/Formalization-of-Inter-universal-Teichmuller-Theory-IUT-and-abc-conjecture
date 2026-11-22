import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge7Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge10Actual — additive maxDegP bounds (real lemmas)

Real Lean (no sorry/axiom): the P1 maximal degree of a union (resp. one-point insertion) is
at most the sum of the maximal degrees of the parts.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge10Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_union_le_sum (S T : Finset (P1Point Qbar)) :
    maxDegP (S ∪ T) <= maxDegP S + maxDegP T := by
  rw [maxDegP_union]
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem maxDegP_insert_le_sum (S : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (insert p S) <= degP p + maxDegP S := by
  rw [maxDegP_insert]
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

def p1MeasureBridge10Rows : List (String × String) :=
  [ ("maxDegP_union_le_sum", "PROVED"), ("maxDegP_insert_le_sum", "PROVED") ]

theorem p1MeasureBridge10Rows_length : p1MeasureBridge10Rows.length = 2 := rfl

#check maxDegP_union_le_sum
#check maxDegP_insert_le_sum

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge10Actual
end
