/- U-C: sQ support positivity shims, attempt with explicit named lemma arguments. -/
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- PROVED: bad F-fiber primes are nonzero (explicit named iff). -/
theorem badFPrimeSet_ne_bot
    (P : Ideal (NumberField.RingOfIntegers T.arithmetic.F))
    (hP : P ∈ badFPrimeSet T) : P ≠ ⊥ := by
  unfold badFPrimeSet at hP
  rcases Finset.mem_biUnion.mp hP with ⟨b, _, hPb⟩
  let p : Ideal (NumberField.RingOfIntegers T.arithmetic.Fmod) :=
    b.1.maximalIdeal.asIdeal
  have hp : p ≠ ⊥ := b.1.maximalIdeal.ne_bot
  have hmem : P ∈ p.primesOver (NumberField.RingOfIntegers T.arithmetic.F) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp
      (NumberField.RingOfIntegers T.arithmetic.F)).mp hPb
  exact Ideal.ne_bot_of_mem_primesOver hp hmem

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity2Actual
end
