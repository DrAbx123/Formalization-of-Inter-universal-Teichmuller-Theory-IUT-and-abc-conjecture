/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedSpanActual
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: localized principal line (statement re-export) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanProofActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanActual

variable {k : Type} [Field k] [NumberField k]

def localizedSpanProofRows : List (String × String × String) :=
  [ ("LocalizedSpanStatement", "localizedLine (spanSingleton x) v = span O_v {algebraMap x}", "GAP (Set/Submodule coercion; no longer needed: use IsPrincipal generator instead)") ]

theorem localizedSpanProofRows_length : localizedSpanProofRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanProofActual

end