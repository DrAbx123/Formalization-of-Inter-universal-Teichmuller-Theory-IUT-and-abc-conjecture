import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p) (q : FinitePlaceQCandidate place.val)

example : CommonPrimeCompletion place = Completion place.val := rfl

example : (CommonPrimeCompletion place)ˣ = (Completion place.val)ˣ := rfl

variable (u : (CommonPrimeCompletion place)ˣ)

example : (u : CommonPrimeCompletion place) = (u : Completion place.val) := rfl

example : (u : Completion place.val) = (u : Completion place.val) := rfl

example : (Units.val u : CommonPrimeCompletion place) = (Units.val u : Completion place.val) := rfl
