import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepProviderP1MeasureActual — f4b finite step -> P1 measure decrease

Genuine new bridge: for P1 states that are finite images of a finite Qbar-set,
the finite step-target measure decrease (measure_stepSet_lt) transfers to the
P1 lexicographic measure (maxDegP, numMaxP).  This closes the f4b finite-count
part of the StepProvider P1 measure input on image states; the general P1 step
transport remains the named StepProvider input.
No closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderP1MeasureActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual

attribute [instance] Classical.decEq


/-- The P1 step target of a finite image is the finite step target, imaged. -/
theorem stepSetP1_image_some (S : Finset Qbar) (alpha0 : Qbar) :
    stepSetP1 (S.image (fun z => P1Point.ofFinite z)) alpha0 =
      (stepSet S alpha0).image (fun z => P1Point.ofFinite z) := by
  ext p
  cases p with
  | none =>
      simp [stepSetP1, stepSet, f0Map, polyMapQbar, f0Map_finite,
        Finset.image_union, Finset.image_image, Finset.mem_image, Finset.mem_union]
  | some z =>
      simp [stepSetP1, stepSet, f0Map, polyMapQbar, f0Map_finite,
        Finset.image_union, Finset.image_image, Finset.mem_image, Finset.mem_union]

/-- Finite f4b step measure decrease transfers to the P1 lexicographic measure. -/
theorem p1MeasureTransfer_of_finite (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) (h2 : 2 ≤ degQ alpha0) :
    Prod.Lex (· < ·) (· < ·)
      (maxDegP (stepSetP1 (S.image (fun z => P1Point.ofFinite z)) alpha0),
        numMaxP (stepSetP1 (S.image (fun z => P1Point.ofFinite z)) alpha0))
      (maxDegP (S.image (fun z => P1Point.ofFinite z)),
        numMaxP (S.image (fun z => P1Point.ofFinite z))) := by
  have h := measure_stepSet_lt S alpha0 halpha0 hmax h2
  rw [stepSetP1_image_some, maxDegP_image_ofFinite, numMaxP_image_ofFinite,
    maxDegP_image_ofFinite, numMaxP_image_ofFinite]
  exact h

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderP1MeasureActual

end
