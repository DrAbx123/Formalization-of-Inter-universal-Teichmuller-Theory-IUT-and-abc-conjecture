import tmp.sheaf.xif.paper.Hull12Ob9BoundTransferActual
import tmp.sheaf.xif.paper.Hull13H7Ob9ComparisonConsumerActual
import tmp.sheaf.xif.paper.Hull13TwoSidedBoundActual

/-!
# ShehddHullOb9ConsumerActual — H7/Ob9 one-sided + two-sided consumer composition

STEP 0 prior-art (reuse only):
* Hull12Ob9BoundTransferActual: hull12_upperBound_transfer (one-sided transfer);
* Hull13H7Ob9ComparisonConsumerActual: HullH7Ob9ComparisonInputs and
  hull13_h7ob9_comparison (Cor312HullDetConclusion + base upper bound);
* Hull13TwoSidedBoundActual: HullH7Ob9TwoSidedInputs and hull13_twoSided_bound
  (adds explicit lower bound at the iterate).

This file gives the consumer-facing bridge between the two input shapes: two-sided
inputs yield the one-sided comparison consumer (base upper bound), and both have the
two-sided iterate bound.  No new assumptions, no sorry/axiom; the arbitrary-iterate
independence (deep Ob9) stays NAMED.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddHullOb9ConsumerActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
open LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **PROVED composition:** two-sided H7/Ob9 inputs give the one-sided comparison
consumer: the Cor 3.12 hull+det conclusion and the base possible-image upper bound. -/
theorem hull_ob9_onesided_of_twosided
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.comparison.consumer.base) →
        z ≤ In.comparison.bound) :=
  hull13_h7ob9_comparison (M := M) I In.comparison

/-- **PROVED composition:** two-sided inputs give the full two-sided consumer
(conclusion + base upper bound + lower/upper at the iterate). -/
theorem hull_ob9_twosided_full
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.comparison.consumer.base) →
        z ≤ In.comparison.bound) ∧
      (∀ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
          In.comparison.consumer.base)) →
        In.lowerBound ≤ w ∧ w ≤ In.comparison.bound) :=
  hull13_twoSided_bound (M := M) I In

/-- Row record: reused one-sided/two-sided consumers vs the composed bridge. -/
def hullOb9ConsumerRows : List (String × String × String) :=
  [ ("one-sided transfer + comparison consumer", "REUSED PROVED", "Hull12.hull12_upperBound_transfer + Hull13.hull13_h7ob9_comparison")
  , ("two-sided consumer (explicit lower bound at iterate)", "REUSED PROVED", "Hull13TwoSided.hull13_twoSided_bound")
  , ("two-sided inputs => one-sided comparison consumer", "COMPOSED PROVED", "hull_ob9_onesided_of_twosided")
  , ("two-sided inputs => full two-sided consumer", "COMPOSED PROVED", "hull_ob9_twosided_full")
  , ("arbitrary log-link iterate independence (deep Ob9)", "NAMED", "Hull12/Hull13 row records; not formalized") ]

theorem hullOb9ConsumerRows_length : hullOb9ConsumerRows.length = 5 := rfl

#check hull_ob9_onesided_of_twosided
#check hull_ob9_twosided_full
#check hullOb9ConsumerRows_length

end LeanFormal.IUT.XiFPaper.ShehddHullOb9ConsumerActual
end
