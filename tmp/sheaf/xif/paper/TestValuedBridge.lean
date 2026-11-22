import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open scoped NormedField

namespace TestValuedBridge
variable {l : PrimeGeFive} (I : OriginalInput.{0,0,0,0,0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

example : Valued (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (WithZero (Multiplicative Int)) :=
  inferInstanceAs (Valued (Completion place.val) (WithZero (Multiplicative Int)))

end TestValuedBridge