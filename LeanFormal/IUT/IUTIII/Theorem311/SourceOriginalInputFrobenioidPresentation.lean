import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Iut.Foundations.SourceModelFrobenioidPresentation

/-!
# The global Example 3.6(ii) Frobenioid attached to an OriginalInput

This IUTIII bridge consumes the production IUTII backend presentation at the
arithmetic base field Fmod of an actual Theorem 3.11 OriginalInput. It does not
construct Hodge theaters, prime-strips or the Example 3.6(iii) comparison.
-/

noncomputable section

namespace LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui

open LeanFormal.IUT.IUTII.Frobenioid.Example36

/-- The global Frobenioid of IUT III, Example 3.6, (ii) attached to the
arithmetic base field Fmod of a Theorem 3.11 input. -/
noncomputable def sourceOriginalInputFrobenioidPresentation
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Iut.FrobenioidPresentation :=
  SourceModelBackend.numberFieldFrobenioidPresentation
    (F := I.initial.arithmetic.Fmod)

end LeanFormal.IUT.Theorem311Source
