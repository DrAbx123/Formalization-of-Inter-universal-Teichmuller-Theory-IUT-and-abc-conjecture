/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: additivity of the count exponent -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountAddActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

def CountAddStatement : Prop :=
  forall (v : NumberField.FinitePlace k) (I J : LineBundle (k := k)),
    I ≠ 0 -> J ≠ 0 ->
      countExponent (k := k) v (I * J) =
        countExponent (k := k) v I + countExponent (k := k) v J

theorem countAdd_proved : CountAddStatement (k := k) := by
  intro v I J hI hJ
  exact countExponent_mul (k := k) v I J hI hJ

def countAddRows : List (String × String × String) :=
  [ ("CountAddStatement", "count_v(I*J) = count_v I + count_v J", "PROVED") ]

theorem countAddRows_length : countAddRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountAddActual

end
