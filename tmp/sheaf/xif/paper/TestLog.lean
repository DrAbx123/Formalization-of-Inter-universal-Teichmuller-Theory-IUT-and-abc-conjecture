import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open scoped NormedField
namespace TestLog
variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
noncomputable instance : Valued (CommonPrimeCompletion (K := K) place) (WithZero (Multiplicative Int)) :=
  inferInstanceAs (Valued (Completion place.val) (WithZero (Multiplicative Int)))
example (x y : (CommonPrimeCompletion (K := K) place)ˣ) : True := by
  haveI : AddMonoid (Multiplicative Int) := inferInstance
  have h := WithZero.log_mul (x := Valued.v (x : CommonPrimeCompletion (K := K) place)) (y := Valued.v (y : CommonPrimeCompletion (K := K) place)) (by simp) (by simp)
  trivial
end TestLog