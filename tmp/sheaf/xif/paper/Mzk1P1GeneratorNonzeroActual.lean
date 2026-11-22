/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1PaperQPilotLineBundleSourceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: generator nonzero and hH/hO linkage -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorNonzeroActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual

variable {k : Type} [Field k] [NumberField k]

theorem localGeneratorDataOfIsPrincipal_ne_zero
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal]
    (hne : localizedLine (k := k) I v ≠ ⊥) :
    (localGeneratorDataOfIsPrincipal (k := k) I v).generator ≠ 0 := by
  intro hzero
  apply hne
  have hspan := (localGeneratorDataOfIsPrincipal (k := k) I v).span_eq
  rw [hspan, hzero]
  simp

/-- Link a nonzero line bundle `hH` to the localized line being nonzero, when the
line bundle has a nonzero generator. -/
theorem localizedLine_ne_bot_of_localGenerator
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal]
    (hgen : (localGeneratorDataOfIsPrincipal (k := k) I v).generator ≠ 0) :
    localizedLine (k := k) I v ≠ ⊥ := by
  intro hbot
  apply hgen
  have hspan := (localGeneratorDataOfIsPrincipal (k := k) I v).span_eq
  have hspanbot : Submodule.span (PaperDeterminantLogVolume.LocalRing (k := k) v)
      {(localGeneratorDataOfIsPrincipal (k := k) I v).generator} = ⊥ := by
    rw [← hspan]
    exact hbot
  simpa using hspanbot

def generatorNonzeroRows : List (String × String × String) :=
  [ ("localGeneratorDataOfIsPrincipal_ne_zero", "localizedLine != bot => generator != 0", "PROVED"),
    ("localizedLine_ne_bot_of_localGenerator", "generator != 0 => localizedLine != bot", "PROVED") ]

theorem generatorNonzeroRows_length : generatorNonzeroRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorNonzeroActual
