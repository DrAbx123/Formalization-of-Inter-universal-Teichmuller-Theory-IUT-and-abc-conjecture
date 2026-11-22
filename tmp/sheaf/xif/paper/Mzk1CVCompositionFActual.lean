import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import Mathlib.Tactic

/-! # Mzk1CVCompositionFActual — CVCompositionLawF PROVED (f' comp f0 critical-value inclusion)

STEP 0 prior-art: Mzk1NestedInductionStepProviderActual (CVCompositionLawF definition,
stepTransport_of_goal conditional on it, f0Map_comp); Mathlib derivative_comp/aeval_comp.

SCOPE: real proof of the F-level CV composition law (point form); it discharges the named
hypothesis of abc minpoly transport stepTransport_of_goal.  No closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CVCompositionFActual

/-- Local name for the F = Qbar used by the minpoly-side definitions. -/
abbrev FF : Type := LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual.F

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open scoped Classical

/-- CV composition law over F = Qbar (point form): a critical point of r o q is a
critical point of q or maps to a critical point of r.  PROVED from the chain rule. -/
theorem cvCompositionLawF_proved : CVCompositionLawF := by
  intro q r z h
  rw [Polynomial.derivative_comp, Polynomial.aeval_mul, Polynomial.aeval_comp] at h
  exact mul_eq_zero.mp h

/-- Target transport (minpoly side) with the named CV input DISCHARGED. -/
theorem stepTransport_of_goal_proved
    {S : Finset (P1Point FF)} {beta : P1Point FF} {q : Polynomial FF}
    {S' : Finset (P1Point FF)} (hqpos : 0 < q.natDegree)
    (hmap : forall p : P1Point FF, p ∈ S -> f0Map q p ∈ S')
    (hcvS : forall z : FF,
      (Polynomial.aeval z) (Polynomial.derivative q) = 0 ->
        P1Point.ofFinite ((Polynomial.aeval z) q) ∈ S')
    (hgoal : LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual.PaperScopeLemma24Target S' (f0Map q beta)) :
    LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual.PaperScopeLemma24Target S beta :=
  stepTransport_of_goal cvCompositionLawF_proved hqpos hmap hcvS hgoal

/-- Rows. -/
def cvCompositionFRows : List (String × String × String) :=
  [ ("CVCompositionLawF (F=Qbar point form)", "PROVED", "cvCompositionLawF_proved (derivative_comp + aeval_mul/aeval_comp)")
  , ("minpoly transport with CV law discharged", "PROVED", "stepTransport_of_goal_proved (consumes abc stepTransport_of_goal)")
  , ("closure", "NOT CLAIMED", "gate NOT PASSED; binding HOLD") ]

theorem cvCompositionFRows_length : cvCompositionFRows.length = 3 := rfl

#check cvCompositionLawF_proved
#check stepTransport_of_goal_proved

end LeanFormal.IUT.XiFPaper.Mzk1CVCompositionFActual
end