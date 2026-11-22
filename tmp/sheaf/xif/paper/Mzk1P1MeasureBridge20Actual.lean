import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge19Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge20Actual — union-insert distribution laws (real)

Real Lean (no sorry/axiom): distribution of union over insertion for the P1 measure, used in
the step-target decompositions.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge20Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_insert_union (S T : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (insert p (S ∪ T)) = max (degP p) (max (maxDegP S) (maxDegP T)) := by
  rw [maxDegP_insert, maxDegP_union]

theorem maxDegP_union_insert (S T : Finset (P1Point Qbar)) (p : P1Point Qbar) :
    maxDegP (S ∪ insert p T) = max (maxDegP S) (max (degP p) (maxDegP T)) := by
  rw [maxDegP_union, maxDegP_insert]

def p1MeasureBridge20Rows : List (String × String) :=
  [ ("maxDegP_insert_union", "PROVED"), ("maxDegP_union_insert", "PROVED") ]

theorem p1MeasureBridge20Rows_length : p1MeasureBridge20Rows.length = 2 := rfl

#check maxDegP_insert_union

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge20Actual
end
