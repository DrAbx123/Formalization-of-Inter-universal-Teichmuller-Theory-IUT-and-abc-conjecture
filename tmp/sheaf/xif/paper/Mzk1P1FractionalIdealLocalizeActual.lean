/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1GeneratorCountActual
import tmp.sheaf.xif.paper.Mzk1LocalizedLineMulActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: fractional ideal localization via num/den -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1FractionalIdealLocalizeActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalizedLineMulActual

variable {k : Type} [Field k] [NumberField k]

/-- Localization of a fractional ideal via num/den decomposition. -/
def FractionalLocalizeStatement (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) : Prop :=
  exists a : NumberField.RingOfIntegers k,
    a ∈ nonZeroDivisors (NumberField.RingOfIntegers k) ∧
      localizedLine (k := k) I v =
        localizedLine (k := k)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
            ((algebraMap (NumberField.RingOfIntegers k) k a) ^ (-1 : Int))) v *
        localizedLine (k := k) (I.num : LineBundle (k := k)) v

def fractionalLocalizeRows : List (String × String × String) :=
  [ ("FractionalLocalizeStatement", "localize I = localize(den^-1) * localize(num)", "GAP (requires LocalizedLineMulLaw)"),
    ("numDenDecomposition", "I = spanSingleton(a^-1) * num", "PROVED") ]

theorem fractionalLocalizeRows_length : fractionalLocalizeRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1FractionalIdealLocalizeActual

end
