import tmp.sheaf.xif.paper.Node09AbsNormRatActual
import tmp.sheaf.xif.paper.Node09HqMultConsumerActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Node09AbsNormRatActual

namespace LeanFormal.IUT.XiFPaper.Node09HlogpTransportActual

/-- hlogp for the Fmod = Q case, given a rational-place model of the bad places
and the two exact transport inputs. -/
theorem hlogp_fmod_rat {l : PrimeGeFive} (X : N8NativeInput l) {p : Nat} [Fact p.Prime]
    (b : FinitePlaceAtPrime ℚ p → Bad (nativePlaceSelection X.S))
    (placeOf : FinitePlaceAtPrime ℚ p → NumberField.FinitePlace ℚ)
    (hcastResidue : ∀ i : FinitePlaceAtPrime ℚ p,
      residueNormBase (b i).1 = residueNormBase (placeOf i))
    (hprime : ∀ i : FinitePlaceAtPrime ℚ p,
      (completionRationalPrime (placeOf i)).val =
        (completionRationalPrime (i.val)).val) :
    ∀ i : FinitePlaceAtPrime ℚ p,
      Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
        Real.log (residueNormBase (b i).1) := by
  intro i
  rw [hcastResidue i]
  exact hlogp_rat_of_place_prime_eq i (hprime i)

/-- Exact remaining missing for the Fmod = Q hlogp transport. -/
def Node09HlogpTransportRemainingMissing : List String :=
  [ "placeOf: rational-place model of the bad places (Fmod = Q base-field transport)",
    "hcastResidue: residueNormBase (b i).1 = residueNormBase (placeOf i)",
    "hprime: place-prime compatibility of placeOf i with i.val" ]

end LeanFormal.IUT.XiFPaper.Node09HlogpTransportActual
