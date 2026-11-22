/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedIsPrincipalActual
import Mathlib.Tactic

/-! # P1: direct instance attempt for localizedLine.IsPrincipal -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalInstanceAttemptActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- Direct typeclass synthesis failed: Mathlib does not infer
`(localizedLine I v).IsPrincipal` from the PID instance on the DVR. -/
def MissingLocalizedIsPrincipalInstance
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  (localizedLine (k := k) I v).IsPrincipal

def instanceAttemptRows : List (String × String × String) :=
  [ ("localizedLine_isPrincipal_attempt", "inferInstance", "FAILED (synthInstanceFailed)"),
    ("MissingLocalizedIsPrincipalInstance", "exact missing instance", "GAP (not asserted)") ]

theorem instanceAttemptRows_length : instanceAttemptRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalInstanceAttemptActual
