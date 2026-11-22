import tmp.sheaf.xif.paper.Mzk1P1FinitePartMeasureActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge2Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepProviderStrictActual — f4b transfer: P1 strict numMax from the finite lemma

Real Lean (no sorry/axiom): given the finite-part decomposition of the P1 step target (image
of the finite stepSet, optionally with infinity) and the PROVED finite strict-count lemma
numMax_stepSet_lt, the P1 maximal count strictly drops on the stable-max-degree branch.
The remaining hypotheses are exactly the set-decomposition bookkeeping of stepSetP1; they are
discharged separately (Mzk1P1StepProviderDecomposition).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartMeasureActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge2Actual

attribute [local instance] Classical.decEq

universe u

/-- f4b transfer: P1 strict count drop from the finite strict-count lemma, modulo the
P1/finite step-target decomposition (image form or image + infinity form). -/
theorem numMaxP_stepSetP1_lt_of_finite
    (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (h2 : 2 <= maxDegP S)
    (halpha0S : P1Point.ofFinite alpha0 ∈ S)
    (hdeg : degQ alpha0 = maxDegP S)
    (hstep : stepSetP1 S alpha0 =
        (stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x) ∨
      stepSetP1 S alpha0 =
        insert P1Point.infty ((stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x)))
    (halphaF : alpha0 ∈ finitePart S)
    (hmaxF : degQ alpha0 = maxDeg (finitePart S))
    (h2F : 2 <= maxDeg (finitePart S))
    (hsameF : maxDeg (stepSet (finitePart S) alpha0) = maxDeg (finitePart S)) :
    numMaxP (stepSetP1 S alpha0) < numMaxP S := by
  have hnumS : numMaxP S = numMax (finitePart S) :=
    numMaxP_eq_numMax_finitePart S h2
  have hstrict : numMax (stepSet (finitePart S) alpha0) < numMax (finitePart S) :=
    numMax_stepSet_lt (finitePart S) alpha0 halphaF hmaxF (by rw [hmaxF]; exact h2F) hsameF
  rcases hstep with hstep | hstep
  · rw [hstep]
    rw [numMaxP_image_ofFinite]
    rw [hnumS]
    exact hstrict
  · rw [hstep]
    have h2st : 2 <= maxDeg (stepSet (finitePart S) alpha0) := by
      rw [hsameF]
      exact h2F
    rw [numMaxP_insert_infty_image (stepSet (finitePart S) alpha0) h2st]
    rw [hnumS]
    exact hstrict

#check numMaxP_stepSetP1_lt_of_finite

end LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictActual
end
