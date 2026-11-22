import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge9Actual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge10Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepComponentBoundsActual — component bounds for the concrete f0 step target

Real Lean (no sorry/axiom): elementary degree/count bounds for the two components of the
concrete step target stepSetP1 (image under f0 and image of critical values), using the
PROVED elementary measure bounds.  These are the reusable estimates for the f4b analysis.
Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepComponentBoundsActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge9Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge10Actual

attribute [local instance] Classical.decEq

universe u

/-- Count bound for the f0-image component. -/
theorem numMaxP_f0Component_le_card (S : Finset (P1Point Qbar)) (alpha0 : Qbar) :
    numMaxP ((S ∪ (conjSet alpha0).image (fun x => P1Point.ofFinite x)).image (f0Map alpha0))
      <= (S ∪ (conjSet alpha0).image (fun x => P1Point.ofFinite x)).card :=
  numMaxP_le_card _

/-- Count bound for the critical-value component. -/
theorem numMaxP_critComponent_le_card (alpha0 : Qbar) :
    numMaxP ((critSet alpha0).image
      (fun x => P1Point.ofFinite (aeval x (minpoly ℚ alpha0)))) <= (critSet alpha0).card :=
  numMaxP_le_card _

/-- Max-degree bound for a union of two finite images. -/
theorem maxDegP_component_union_le (S : Finset Qbar) (T : Finset (P1Point Qbar)) :
    maxDegP ((S.image (fun z => P1Point.ofFinite z)) ∪ T) <=
      maxDeg S + maxDegP T := by
  rw [maxDegP_union]
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

def p1StepComponentBoundsRows : List (String × String) :=
  [ ("numMaxP_f0Component_le_card", "PROVED"), ("numMaxP_critComponent_le_card", "PROVED"),
    ("maxDegP_component_union_le", "PROVED") ]

theorem p1StepComponentBoundsRows_length : p1StepComponentBoundsRows.length = 3 := rfl

#check numMaxP_f0Component_le_card
#check maxDegP_component_union_le

end LeanFormal.IUT.XiFPaper.Mzk1P1StepComponentBoundsActual
end
