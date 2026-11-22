import tmp.sheaf.xif.paper.S1504SourceLineBundleCarrierActual
import tmp.sheaf.xif.paper.S1423ThetaInvertibleActual

/-! # S1517: the exact missing localization map for the paper line bundle

S1504 reduced the paper carrier to

```text
localization : (v : FinitePlace S.arithmetic.Fmod) ->
  s1423Module S -> Completion v
```

for the actual S1423 puncture module.  This file records why that map is not
produced by S1423 or by the actual completion embedding, and names the exact
first missing map.

The S1423 module is an ideal of the coordinate ring `R` over `S.arithmetic.F`,
while the paper completion is at a finite place `v` of `S.arithmetic.Fmod`.
The actual completion embedding is

```text
algebraMap (S.arithmetic.Fmod) (Completion v),
```

not a map out of `R`: `F` is a finite Galois extension of `Fmod` and the
completion of `Fmod` at `v` does not receive `F` without an additional place
`w | v` of `F` and an `Fmod`-embedding.  S1423 supplies the rank-one projective
module and its Picard class, but no such section localization.  Consequently no
carrier localization is fabricated by zero or by a constant map.

Given the exact map, S1504's carrier and QPilotObject fill are actual; this file
only aliases that conditional construction and records the missing map. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1517SourceLineBundleLocalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1504SourceLineBundleCarrierActual
open ABCBridge.S1423ThetaInvertibleActual

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

/-- The exact first missing map: the section localization of the actual S1423
puncture module into every completion of `Fmod`.  No inhabitant is asserted. -/
abbrev S1517MissingLocalization : Type (max u 0) :=
  S1504LocalizationData S

/-- Given the exact localization, the paper carrier is the S1504 carrier with
the actual S1423 puncture module as its section type. -/
noncomputable def s1517Carrier (L : S1517MissingLocalization S) :
    PaperLineBundleCarrier (k := S.arithmetic.Fmod) :=
  carrierOfLocalization S L

@[simp] theorem s1517Carrier_total (L : S1517MissingLocalization S) :
    (s1517Carrier S L).total = s1423Module S := rfl

/-- The exact identification is the equality of the carrier's section type with
the S1423 puncture module. -/
theorem s1517Carrier_identified (L : S1517MissingLocalization S) :
    PaperLineBundleIdentified S (s1517Carrier S L) :=
  carrierOfLocalization_identified S L

/-- The carrier's localization is exactly the supplied missing map; this records
that no zero or constant localization is inserted by the construction. -/
@[simp] theorem s1517Carrier_localization (L : S1517MissingLocalization S)
    (v : NumberField.FinitePlace S.arithmetic.Fmod) (x : s1423Module S) :
    (s1517Carrier S L).localization v x = L.localization v x := rfl

end LeanFormal.IUT.XiFPaper.S1517SourceLineBundleLocalizationActual
end
