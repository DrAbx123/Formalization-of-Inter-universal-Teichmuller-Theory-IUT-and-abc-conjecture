import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
variable (u : (CommonPrimeCompletion place)ˣ)

#check Units (Completion place.val)
#check Units (CommonPrimeCompletion place)
#check (inferInstance : Monoid (Completion place.val))
#check (inferInstance : Monoid (CommonPrimeCompletion place))
#check (u : Units (Completion place.val))
