import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

/-! # S1214: actual stripOfChoice for an arbitrary OriginalInput

For any source input I : OriginalInput l V, Choice = I.family.index, and

  stripOfChoice I i := I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2

is an actual map from the source Choice type to actual F-prime-strips.
This is the first actual component needed for a SourceRun on
Choice = I.family.index.  No concrete SourceDefinition31Data / OriginalInput is
constructed; I remains an arbitrary input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1214StripOfChoiceActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual F-prime-strip attached to a source Choice index. -/
noncomputable def stripOfChoice (i : I.family.index) :
    FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2

/-- On canonical lattice indices this is the actual fPrimeStripAt. -/
theorem stripOfChoice_indexOf (n m : Int) :
    stripOfChoice (I := I) (I.indexOf n m) = I.fPrimeStripAt n m := by
  unfold stripOfChoice
  rw [I.indexOf_apply]

/-- Every actual lattice F-prime-strip is hit by stripOfChoice. -/
theorem stripOfChoice_surjective_at (n m : Int) :
    ∃ i : I.family.index, stripOfChoice (I := I) i = I.fPrimeStripAt n m :=
  ⟨I.indexOf n m, stripOfChoice_indexOf (I := I) n m⟩

/-- Horizontal shift compatibility: the choice-level shift maps to the
corresponding shifted actual F-prime-strip. -/
theorem stripOfChoice_horizontalShift (i : I.family.index) :
    stripOfChoice (I := I) (I.horizontalShift i) =
      I.fPrimeStripAt (horizontalIndex (I.index_equiv i)).1
        (horizontalIndex (I.index_equiv i)).2 := by
  unfold stripOfChoice
  rw [I.horizontalShift_index]

/-- Vertical shift compatibility. -/
theorem stripOfChoice_verticalShift (i : I.family.index) :
    stripOfChoice (I := I) (I.verticalShift i) =
      I.fPrimeStripAt (verticalIndex (I.index_equiv i)).1
        (verticalIndex (I.index_equiv i)).2 := by
  unfold stripOfChoice
  rw [I.verticalShift_index]

/-- The canonical Choice type for a SourceRun on the actual source input. -/
abbrev SourceChoice : Type _ := I.family.index

end LeanFormal.IUT.XiFPaper.S1214StripOfChoiceActual
end