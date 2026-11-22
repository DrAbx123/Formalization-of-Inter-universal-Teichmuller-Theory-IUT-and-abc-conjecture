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

example : ((u : Units (Completion place.val)) : Completion place.val) = (u : CommonPrimeCompletion place) := rfl

example : (@Units.val (Completion place.val) _ (u : Units (Completion place.val)) : Completion place.val) =
    (u : CommonPrimeCompletion place) := rfl

example : (Units.val (u : Units (Completion place.val)) : Completion place.val) =
    (u : CommonPrimeCompletion place) := rfl

example (h : u = u) : True := by trivial
