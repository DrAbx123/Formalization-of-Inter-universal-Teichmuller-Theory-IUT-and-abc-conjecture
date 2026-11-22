import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureBridgeActual — real P1 measure bridge lemmas

Real Lean (no sorry/axiom): P1 maximal degree / count of finite images coincide with the
finite measure, plus the insert-infinity degree law.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridgeActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

/-- P1 maximal degree of the finite image of a finite point set equals the finite maxDeg. -/
theorem maxDegP_image_ofFinite_reexport (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) = maxDeg S :=
  maxDegP_image_ofFinite S

/-- P1 maximal count of the finite image of a finite point set equals the finite numMax. -/
theorem numMaxP_image_ofFinite_reexport (S : Finset Qbar) :
    numMaxP (S.image (fun z => P1Point.ofFinite z)) = numMax S :=
  numMaxP_image_ofFinite S

/-- Adding the point at infinity (degree 1) gives P1 maximal degree max 1 (maxDeg S). -/
theorem maxDegP_insert_infty_image (S : Finset Qbar) :
    maxDegP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) =
      max 1 (maxDeg S) := by
  unfold maxDegP maxDeg
  rw [Finset.sup_insert, Finset.sup_image]
  rfl

def p1MeasureBridgeRows : List (String × String) :=
  [ ("maxDegP_image_ofFinite_reexport", "PROVED (reuse)"),
    ("numMaxP_image_ofFinite_reexport", "PROVED (reuse)"),
    ("maxDegP_insert_infty_image", "PROVED (new)") ]

theorem p1MeasureBridgeRows_length : p1MeasureBridgeRows.length = 3 := rfl

#check maxDegP_image_ofFinite_reexport
#check maxDegP_insert_infty_image

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridgeActual
end
