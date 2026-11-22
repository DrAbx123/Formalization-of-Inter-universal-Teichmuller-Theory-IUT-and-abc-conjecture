/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorUncondActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineNonzeroActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorUncondActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

theorem localizedLine_ne_bot_of_generator_uncond
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (hgen : (localGeneratorUncond I v).generator ≠ 0) :
    localizedLine (k := k) I v ≠ ⊥ := by
  intro hbot
  apply hgen
  have hspan := (localGeneratorUncond I v).span_eq
  have hspanbot : Submodule.span (LocalRing (k := k) v)
      {(localGeneratorUncond I v).generator} = ⊥ := by
    rw [← hspan]
    exact hbot
  simpa using hspanbot

def localizedNonzeroRows : List (String × String × String) :=
  [ ("localizedLine_ne_bot_of_generator_uncond", "generator != 0 => localizedLine != bot", "GREEN") ]

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineNonzeroActual
