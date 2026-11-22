/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalNoGapActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

theorem localizedLine_isPrincipal_noGap
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    (localizedLine (k := k) I v).IsPrincipal :=
  localizedLine_isPrincipal_actual (k := k) I v

def noGapRows : List (String × String × String) :=
  [ ("localizedLine_isPrincipal_noGap", "MissingLocalizedIsPrincipal removed", "GREEN") ]

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedIsPrincipalNoGapActual
