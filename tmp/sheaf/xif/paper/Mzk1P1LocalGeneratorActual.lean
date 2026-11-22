/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import Mathlib.Tactic

/-! # P1: actual generator of the localized line (LFI official) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual

variable {k : Type} [Field k] [NumberField k]

/-- Actual LocalGeneratorData from the DVR IsPrincipal instance (no assumptions). -/
noncomputable def localGeneratorDataOfIsPrincipal (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) : LocalGeneratorData (k := k) I v := by
  classical
  haveI : (localizedLine (k := k) I v).IsPrincipal :=
    localizedLine_isPrincipal_actual (k := k) I v
  exact
    { generator := Submodule.IsPrincipal.generator (localizedLine (k := k) I v)
      span_eq := (Submodule.IsPrincipal.span_singleton_generator (localizedLine (k := k) I v)).symm }

/-- LocalPrincipalGenerator without extra hypotheses. -/
theorem localPrincipalGenerator_proved (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    LocalPrincipalGenerator (k := k) I v :=
  ⟨localGeneratorDataOfIsPrincipal (k := k) I v⟩

def localGeneratorRows : List (String × String × String) :=
  [ ("localGeneratorDataOfIsPrincipal", "LocalGeneratorData no hypotheses", "CONSTRUCTED (LFI IsPrincipal)"),
    ("localPrincipalGenerator_proved", "LocalPrincipalGenerator no hypotheses", "PROVED") ]

theorem localGeneratorRows_length : localGeneratorRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorActual

end