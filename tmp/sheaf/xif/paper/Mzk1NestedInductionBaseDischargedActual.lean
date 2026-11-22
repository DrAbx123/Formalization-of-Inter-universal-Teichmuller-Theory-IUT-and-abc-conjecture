import Mathlib
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionBaseCaseActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import LeanFormal.IUT.Audit.Status

/-!
# Mzk1NestedInductionBaseDischargedActual — paper-scope 2.4 assembly with base PROVIDED

STEP 0 prior-art: reuse Mzk1NestedInductionActual.paperScopeLemma24Statement_of_providers
(two-provider assembly over the proved well-founded lexicographic induction) and
Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved (the identity-polynomial
base provider, unconditional).  The StepProvider remains the named geometric layer
(Mzk1NestedInductionStepProviderActual records the minpoly side + named avoidance).

DELIVERED HERE (no new math, wiring only): the paper-scope Lemma 2.4 statement follows
from the single remaining named input StepProvider.  No closure claim; the geometric
step layer is still named.  Registry frozen 14041.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseDischargedActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseCaseActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- **ASSEMBLY WITH BASE DISCHARGED.** With the base provider now proved
(identity polynomial, unconditional), the paper-scope Lemma 2.4 statement follows from
the single remaining named input: the geometric StepProvider. -/
theorem paperScopeLemma24Statement_of_stepProvider
    (hstep : StepProvider) : PaperScopeLemma24Statement :=
  paperScopeLemma24Statement_of_providers baseCaseProvider_proved hstep

/-- Same statement in the registered DAG alias form. -/
theorem algebraicNestedInductionInput_of_stepProvider
    (hstep : StepProvider) :
    LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual.AlgebraicNestedInductionInput :=
  paperScopeLemma24Statement_of_stepProvider hstep

/-- Row record: what is now proved vs the remaining named input. -/
def baseDischargedRows : List (String × String × String) :=
  [ ("base provider (identity polynomial)", "PROVED", "Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved")
  , ("well-founded (maxDegP, numMaxP) induction", "PROVED", "Mzk1NestedInductionActual.induction_with_invariant / paperScopeLemma24Statement_of_providers")
  , ("assembly with base discharged", "PROVED (conditional on StepProvider)", "paperScopeLemma24Statement_of_stepProvider")
  , ("geometric StepProvider (normalised f0 + avoidance)", "NAMED", "Mzk1NestedInductionStepProviderActual: minpoly side + stepTransport_of_goal conditional; geometric construction/avoidance named") ]

theorem baseDischargedRows_length : baseDischargedRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseDischargedActual
end
