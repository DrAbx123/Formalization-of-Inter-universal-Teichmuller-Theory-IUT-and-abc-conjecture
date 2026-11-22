import tmp.sheaf.xif.paper.S1460SourceFinitePlaceIndexActual
import tmp.sheaf.xif.paper.S1321PaperOriginalInputActual

/-! # S1462: Gaussian OriginalInput with finite-place V — exact first field

S1321's concrete Gaussian `PaperOriginalInput` is

```text
concreteGaussianPaperOriginalInput ... :
  PaperOriginalInput ... l Unit
```

and its underlying `sourceHaarActualOriginalInput` is over `Unit`; the
`sourceHaarActualFamily` prime strips are `Unit`-indexed Haar strips
(`Pi = Multiplicative (Int × Int)`, `Mon = SourceHaarActualValueMonoid`).

Changing only the index type to

```text
V := NumberField.FinitePlace (S1280Arithmetic l).Fmod
```

while keeping the family requires a V-indexed `SourceHodgeTheaterFamily`.
The tree has no such actual family: the S1321/S1280 family is the Unit Haar
family, and reindexing it along the constant map `V -> Unit` would make the
prime strips constant in the place variable, which is not the source-faithful
finite-place family and is not used here.

The exact first field is therefore an actual V-indexed `SourceHodgeTheaterFamily`
over `V = NumberField.FinitePlace (S1280Arithmetic l).Fmod` (equivalently the
corresponding source-faithful Gaussian `OriginalInput`), with its actual
finite-place prime strips.  Given that family, `OriginalInput` over this V has
`Equiv.refl` for `V ≃ FinitePlace Fmod`, and S1460 constructs
`SourceFinitePlaceIndex`, `IntegralInd3PlaceComparison` and the Ind3 carrier
with no constant/arbitrary map.

This file records the exact boundary; it does not alter S1321 and does not
create a constant place map or a fake family. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1462GaussianOriginalInputFinitePlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1321PaperOriginalInputActual
open LeanFormal.IUT.XiFPaper.S1427Ind3PlaceComparisonActual
open LeanFormal.IUT.XiFPaper.S1460SourceFinitePlaceIndexActual

#check concreteGaussianPaperOriginalInput
#check sourceHaarActualOriginalInput
#check sourceHaarActualFamily
#check S1280Arithmetic
#check NumberField.FinitePlace
#check SourceFinitePlaceIndex
#check sourceFinitePlaceIndexOfEquiv
#check actualIntegralInd3PlaceComparison
#check actualInd3Carrier

/-- The intended concrete finite-place index type for the Gaussian input. -/
abbrev S1462GaussianFinitePlaceIndex (l : PrimeGeFive) : Type :=
  NumberField.FinitePlace (S1280Arithmetic l).Fmod

/-- The exact missing V-indexed family: the source-faithful Gaussian
`SourceHodgeTheaterFamily` over the actual finite-place index type. -/
abbrev S1462GaussianFinitePlaceFamily (l : PrimeGeFive) : Type 1 :=
  SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l (S1462GaussianFinitePlaceIndex l)

end LeanFormal.IUT.XiFPaper.S1462GaussianOriginalInputFinitePlaceActual
end
