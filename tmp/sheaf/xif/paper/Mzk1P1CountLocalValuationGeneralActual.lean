/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationProofActual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: general count <-> valuation for integral ideals -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountLocalValuationGeneralActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual

variable {k : Type} [Field k] [NumberField k]

/-- General statement: for an integral ideal, generator valuation = -count. -/
def CountLocalValuationGeneral : Prop :=
  forall (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k),
    IdealLocalizedCountStatement (k := k) I hI v

def countLocalValuationGeneralRows : List (String × String × String) :=
  [ ("CountLocalValuationGeneral", "ideal localized count statement", "GAP: same as IdealLocalizedCount"),
    ("principal case", "localValuation (algebraMap a) = -count_v(span{a})", "PROVED"),
    ("bridges", "3 explicit bridges", "PARTIAL") ]

theorem countLocalValuationGeneralRows_length : countLocalValuationGeneralRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountLocalValuationGeneralActual

end
