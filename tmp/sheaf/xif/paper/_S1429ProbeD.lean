import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p) (q : FinitePlaceQCandidate place.val)
variable (r : NatRootSystem (candidateUnits place q))
variable (n : Nat)

example : (Units.val (r.root n) : Completion place.val) = (r.root n : Completion place.val) := rfl

example : (Units.val (candidateUnits place q) : Completion place.val) = (q.q : Completion place.val) := rfl

example (hpow : r.root n ^ n = candidateUnits place q) :
    (Units.val (r.root n) : Completion place.val) ^ n =
      (Units.val (candidateUnits place q) : Completion place.val) := by
  have h := congrArg (fun u : (CommonPrimeCompletion place)ˣ => (u : CommonPrimeCompletion place)) hpow
  simpa [Units.val_pow_eq_pow_val] using h
