/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedSpanActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: final localized span route (IsPrincipal generator) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanProofFinalActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanActual

variable {k : Type} [Field k] [NumberField k]

def LocalizedSpanFinalTarget : Prop :=
  forall (x : k) (v : NumberField.FinitePlace k),
    LocalizedSpanStatement (k := k) x v

def localizedSpanFinalRows : List (String × String × String) :=
  [ ("LocalizedSpanFinalTarget", "span version (superseded by generator span via IsPrincipal)", "SUPERSEDED"),
    ("generator span", "LocalGeneratorData.span_eq gives localizedLine = span {generator}", "READY (LFI blocker)") ]

theorem localizedSpanFinalRows_length : localizedSpanFinalRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanProofFinalActual

end
