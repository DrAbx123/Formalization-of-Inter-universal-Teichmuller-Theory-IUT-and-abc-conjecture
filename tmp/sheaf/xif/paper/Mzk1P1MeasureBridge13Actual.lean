import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge5Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridge13Actual — P1/finite measure equalities (real)

Real Lean (no sorry/axiom): P1 maximal degree/count of finite images coincide with the
finite measure.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge13Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge5Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDegP_image_eq (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) = maxDeg S :=
  maxDegP_image_ofFinite S

theorem numMaxP_image_eq (S : Finset Qbar) :
    numMaxP (S.image (fun z => P1Point.ofFinite z)) = numMax S :=
  numMaxP_image_ofFinite S

theorem maxDegP_image_le_maxDeg (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) <= maxDeg S :=
  le_of_eq (maxDegP_image_ofFinite S)

def p1MeasureBridge13Rows : List (String × String) :=
  [ ("maxDegP_image_eq", "PROVED"), ("numMaxP_image_eq", "PROVED"),
    ("maxDegP_image_le_maxDeg", "PROVED") ]

theorem p1MeasureBridge13Rows_length : p1MeasureBridge13Rows.length = 3 := rfl

#check maxDegP_image_eq

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge13Actual
end
