import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
variable (q : FinitePlaceQCandidate place.val)

#synth AddMonoid (Multiplicative Int)
#synth Valued (CommonPrimeCompletion place) (WithZero (Multiplicative Int))
#synth Valued (Completion place.val) (WithZero (Multiplicative Int))

example : Valued (CommonPrimeCompletion place) (WithZero (Multiplicative Int)) :=
  inferInstanceAs (Valued (Completion place.val) (WithZero (Multiplicative Int)))

example : (Valued.v (q.q : CommonPrimeCompletion place) : WithZero (Multiplicative Int)) ≠ 0 := by
  haveI : Valued (CommonPrimeCompletion place) (WithZero (Multiplicative Int)) :=
    inferInstanceAs (Valued (Completion place.val) (WithZero (Multiplicative Int)))
  exact q.valuation_ne_zero
