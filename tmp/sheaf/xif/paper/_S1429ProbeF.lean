import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p) (q : FinitePlaceQCandidate place.val)
variable (u : (CommonPrimeCompletion place)ˣ)

-- explicit type argument to Units.val
example : (@Units.val (Completion place.val) _ u : Completion place.val) = (u : Completion place.val) := rfl

example : (Units.val (α := Completion place.val) u : Completion place.val) = (u : CommonPrimeCompletion place) := rfl

-- canonical valuation term transported to the common completion
example : Valuation (CommonPrimeCompletion place) (WithZero (Multiplicative Int)) :=
  (Valued.v : Valuation (Completion place.val) (WithZero (Multiplicative Int)))

example : (let v : Valuation (CommonPrimeCompletion place) (WithZero (Multiplicative Int)) :=
    (Valued.v : Valuation (Completion place.val) (WithZero (Multiplicative Int)))
    v (u : CommonPrimeCompletion place)) = (u : CommonPrimeCompletion place) := rfl
