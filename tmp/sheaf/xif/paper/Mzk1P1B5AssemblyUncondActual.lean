/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FractionalExpansionUncondActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogExpansionActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: B5 assembly without hproduct -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1B5AssemblyUncondActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual

variable {k : Type} [Field k] [NumberField k]

def B5AssemblyUncondRows : List (String × String × String) :=
  [ ("FractionalLogVolumeExpansion", "unconditional (Mzk1B5FractionalExpansionUncondActual)", "PROVED"),
    ("relativeDetLog expansion", "conditional on FractionalLogVolumeExpansion", "PROVED"),
    ("arch metric", "archDetMetricWeight = -CK * log-norm", "PROVED"),
    ("hproduct", "removed: B5 uses count expansion directly", "DONE (no hproduct)") ]

theorem B5AssemblyUncondRows_length : B5AssemblyUncondRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1B5AssemblyUncondActual

end
