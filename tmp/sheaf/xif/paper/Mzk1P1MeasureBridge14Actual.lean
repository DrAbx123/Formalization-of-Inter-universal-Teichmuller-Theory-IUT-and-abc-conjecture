import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge3Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge14Actual — degenerate measure values (real)

Real Lean (no sorry/axiom): the P1 degree measure of the empty set is 0.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge14Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_empty : maxDegP (∅ : Finset (P1Point Qbar)) = 0 := by
  unfold maxDegP
  simp

theorem numMaxP_empty : numMaxP (∅ : Finset (P1Point Qbar)) = 0 := by
  unfold numMaxP
  rw [maxDegP_empty]
  simp

def p1MeasureBridge14Rows : List (String × String) :=
  [ ("maxDegP_empty", "PROVED"), ("numMaxP_empty", "PROVED") ]

theorem p1MeasureBridge14Rows_length : p1MeasureBridge14Rows.length = 2 := rfl

#check maxDegP_empty
#check numMaxP_empty

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge14Actual
end
