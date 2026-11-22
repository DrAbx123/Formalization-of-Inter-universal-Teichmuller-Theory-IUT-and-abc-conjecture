import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

/-! # S1221: actual stripOfChoice for arbitrary OriginalInput

For every `I : OriginalInput l V`, the source index type `I.family.index` maps
to actual F-prime-strips by the source family:

```text
stripOfChoice i := I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2
```

This is the minimal actual Choice-to-strip map.  No concrete initial data is
constructed; `I` is kept as the theorem quantifier.  The induced operation
link is the actual source family link `I.fLinkAt`, not a renamed evaluation. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1221StripOfChoiceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual strip map on the source index type. -/
noncomputable def stripOfChoice (i : I.family.index) :
    FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2

@[simp] theorem stripOfChoice_apply (i : I.family.index) :
    stripOfChoice I i =
      I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2 := rfl

/-- The strip map recovers the source theater strip at the corresponding
lattice point. -/
theorem stripOfChoice_eq_theaterStrip (i : I.family.index) :
    stripOfChoice I i = (I.family.theater i).primeStrip := by
  rw [stripOfChoice_apply, I.fPrimeStripAt_eq]
  congr 1
  simp [OriginalInput.indexOf]

/-- Actual operation link between two Choice indices: the source family link
`I.fLinkAt` at the corresponding lattice points. -/
noncomputable def linkOfChoice (i j : I.family.index) :
    FPrimeStripEquiv (stripOfChoice I i) (stripOfChoice I j) :=
  I.fLinkAt (I.index_equiv i).1 (I.index_equiv i).2
    (I.index_equiv j).1 (I.index_equiv j).2

@[simp] theorem linkOfChoice_apply (i j : I.family.index) :
    linkOfChoice I i j =
      I.fLinkAt (I.index_equiv i).1 (I.index_equiv i).2
        (I.index_equiv j).1 (I.index_equiv j).2 := rfl

end LeanFormal.IUT.XiFPaper.S1221StripOfChoiceActual
end
