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

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineSpanActual

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

theorem localizedLine_span_generator_uncond
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    Submodule.span (LocalRing (k := k) v)
      {(localGeneratorUncond I v).generator} =
      localizedLine (k := k) I v :=
  (localGeneratorUncond I v).span_eq.symm

def localizedSpanRows : List (String × String × String) :=
  [ ("localizedLine_span_generator_uncond", "span{generator} = localizedLine", "GREEN") ]

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineSpanActual
