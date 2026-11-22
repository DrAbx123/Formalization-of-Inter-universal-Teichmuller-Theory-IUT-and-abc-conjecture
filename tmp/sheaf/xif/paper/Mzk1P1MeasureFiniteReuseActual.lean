import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureFiniteReuseActual — reuse record of the finite measure assets

A475: the finite-part measure assets already exist in Mzk1NestedInductionActual.  This file
records them by name and states the transfer statements they cover (reuse, no copying of
theory, no assertion of the missing P1 strict bound).  No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureFiniteReuseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

/-- Reused: finite max-degree non-increase of the step set. -/
theorem finiteMaxDeg_step_reuse (S : Finset Qbar) (alpha0 : Qbar) (h : alpha0 ∈ S)
    (hdeg : degQ alpha0 = maxDeg S) : maxDeg (stepSet S alpha0) <= maxDeg S :=
  maxDeg_stepSet_le S alpha0 h hdeg

/-- Reused: finite P1 image count law. -/
theorem finiteNumMaxP_image_reuse (S : Finset Qbar) :
    numMaxP (S.image (fun z => (some z : P1Point Qbar))) = numMax S :=
  numMaxP_image_ofFinite S

/-- Row record: finite reuse evidence. -/
def p1MeasureFiniteReuseRows : List (String × String) :=
  [ ("maxDeg_stepSet_le", "REUSE (Mzk1NestedInductionActual)"),
    ("numMaxP_image_ofFinite", "REUSE (Mzk1NestedInductionActual:661)"),
    ("numMax_stepSet_lt", "REUSE (finite strict branch; P1 transfer still repo-missing)") ]

theorem p1MeasureFiniteReuseRows_length : p1MeasureFiniteReuseRows.length = 3 := rfl

#check numMax_stepSet_lt
#check maxDeg_stepSet_le

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureFiniteReuseActual
end
