/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual

/-! # P1: LocalGeneratorData from IsPrincipal -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

variable {k : Type} [Field k] [NumberField k]

/-- Build the mainline generator datum from the principal-submodule instance. -/
noncomputable def localGeneratorDataOfIsPrincipal
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal] :
    LocalGeneratorData (k := k) I v where
  generator := Submodule.IsPrincipal.generator (localizedLine (k := k) I v)
  span_eq := (Submodule.IsPrincipal.span_singleton_generator
    (localizedLine (k := k) I v)).symm

theorem localGeneratorDataOfIsPrincipal_generator
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal] :
    (localGeneratorDataOfIsPrincipal (k := k) I v).generator =
      Submodule.IsPrincipal.generator (localizedLine (k := k) I v) := rfl

def localGeneratorRows : List (String × String × String) :=
  [ ("localGeneratorDataOfIsPrincipal", "IsPrincipal => LocalGeneratorData", "CONSTRUCTED"),
    ("localGeneratorDataOfIsPrincipal_generator", "generator projection", "PROVED (rfl)") ]

theorem localGeneratorRows_length : localGeneratorRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual
