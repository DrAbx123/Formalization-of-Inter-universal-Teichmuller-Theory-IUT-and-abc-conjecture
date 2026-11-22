import tmp.sheaf.xif.paper.Mzk1P1CardinalityActual
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
set_option linter.checkUnivs false

/-!
# Mzk1P1SpecialSetBundleActual — P1 special-set bundle

Reuses the EXIT0 P1 cardinality/special-set facts to expose the finite special set
{∞,0,1} with its three membership proofs.  No new math; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetBundleActual

open LeanFormal.IUT.XiFPaper.Mzk1P1CardinalityActual

structure P1SpecialSetBundle : Prop where
  finite : specialSet.Finite
  infty_mem : (none : Option ℂ) ∈ specialSet
  zero_mem : (some (0 : ℂ)) ∈ specialSet
  one_mem : (some (1 : ℂ)) ∈ specialSet

def p1SpecialSetBundle : P1SpecialSetBundle :=
{ finite := specialSet_finite
  infty_mem := infty_mem_specialSet
  zero_mem := zero_mem_specialSet
  one_mem := one_mem_specialSet }

theorem p1SpecialSet_finite_consumer : specialSet.Finite :=
  p1SpecialSetBundle.finite

def p1SpecialSetRows : List (String × String × String) :=
  [ ("special set bundle", "P1SpecialSetBundle", "DEF (reuses EXIT0 P1 facts)"),
    ("finite projection", "p1SpecialSet_finite_consumer", "PROVED"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem p1SpecialSetRows_length : p1SpecialSetRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetBundleActual

end
