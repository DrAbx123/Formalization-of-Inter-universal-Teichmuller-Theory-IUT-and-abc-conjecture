/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: LocalPrincipalGenerator from the IsPrincipal route -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalPrincipalGeneratorProofActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

variable {k : Type} [Field k] [NumberField k]

/-- The IsPrincipal route to LocalPrincipalGenerator. -/
def LocalPrincipalGeneratorViaIsPrincipal : Prop :=
  forall (I : LineBundle (k := k)) (v : NumberField.FinitePlace k),
    LocalPrincipalGenerator (k := k) I v

def localPrincipalGeneratorRows : List (String × String × String) :=
  [ ("LocalPrincipalGeneratorViaIsPrincipal", "LocalPrincipalGenerator without hypotheses", "BLOCKED (LFI red; true construction ready)"),
    ("construction", "IsPrincipal.generator + span_singleton_generator", "READY") ]

theorem localPrincipalGeneratorRows_length : localPrincipalGeneratorRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalPrincipalGeneratorProofActual

end
