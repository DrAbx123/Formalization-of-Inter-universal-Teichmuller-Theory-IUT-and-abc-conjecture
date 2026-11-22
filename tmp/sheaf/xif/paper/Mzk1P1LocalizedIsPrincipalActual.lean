/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5GeneratorCandidateActual
import Mathlib.Tactic

/-! # P1: localizedLine IsPrincipal construction / exact missing -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- Construct `IsPrincipal` for `localizedLine` from an explicit generator and
span equality. -/
theorem localizedLine_isPrincipal_of_span
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (a : LocalField (k := k) v)
    (hspan : localizedLine (k := k) I v =
      Submodule.span (LocalRing (k := k) v) {a}) :
    (localizedLine (k := k) I v).IsPrincipal :=
  ⟨a, hspan⟩

/-- Exact missing instance: the localized line is principal over the DVR. -/
def MissingLocalizedIsPrincipal
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  (localizedLine (k := k) I v).IsPrincipal

def localizedIsPrincipalRows : List (String × String × String) :=
  [ ("localizedLine_isPrincipal_of_span", "explicit generator + span => IsPrincipal", "PROVED"),
    ("MissingLocalizedIsPrincipal", "DVR localization principal-submodule instance", "EXACT MISSING") ]

theorem localizedIsPrincipalRows_length : localizedIsPrincipalRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalActual
