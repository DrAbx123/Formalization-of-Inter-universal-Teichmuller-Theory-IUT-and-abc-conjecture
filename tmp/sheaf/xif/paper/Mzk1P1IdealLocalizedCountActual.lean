/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: localized integral ideal as a uniformizer power (statement) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

/-- Statement: the localization of a nonzero integral ideal at a finite place is the
`e`-th power of the maximal ideal, with `e = count_v(I)`. -/
def IdealLocalizedCountStatement (I : Ideal (NumberField.RingOfIntegers k))
    (_hI : I ≠ 0) (v : NumberField.FinitePlace k) : Prop :=
  ∃ (π : LocalRing (k := k) v) (e : Nat),
    e = ((Associates.mk v.maximalIdeal.asIdeal).count (Associates.mk I).factors) ∧
    localizedLine (k := k) (I : LineBundle (k := k)) v =
      Submodule.span (LocalRing (k := k) v)
        {((π : LocalField (k := k) v) ^ e)}

def idealLocalizedCountRows : List (String × String × String) :=
  [ ("IdealLocalizedCountStatement", "localizedLine ideal = maxIdeal^count", "GAP (DVR localization principal-ideal bridge)"),
    ("missing Mathlib", "IsDiscreteValuationRing + Ideal.map maximal ideal = span uniformizer; count = multiplicity", "GAP list") ]

theorem idealLocalizedCountRows_length : idealLocalizedCountRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual

end