/- U-C: discharge the sQ support positivity hypotheses (extends Positivity2). -/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import tmp.sheaf.xif.paper.Mzk1ULSQPositivity2Actual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField UniqueFactorizationMonoid

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- PROVED: q-support primes are nonzero (badFPrimeSet nonzeroness + underIntGen>=1). -/
theorem qSupportPrimes_ne_zero (p : ℕ) (hp : p ∈ qSupportPrimes T) : p ≠ 0 := by
  rcases Finset.mem_image.mp hp with ⟨P, hP, rfl⟩
  have hPne : P ≠ ⊥ := badFPrimeSet_ne_bot T P hP
  have hge : (1 : ℝ) ≤ ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ) :=
    underIntGen_natAbs_ge_one T hPne
  have hpos : 0 < (underIntGen (K := T.arithmetic.F) P).natAbs := by
    exact_mod_cast hge
  exact Nat.pos_iff_ne_zero.mp hpos

/-- PROVED: d-support primes are nonzero (differentIdeal != bot => P != bot). -/
theorem dSupportPrimes_ne_zero (p : ℕ) (hp : p ∈ dSupportPrimes T) : p ≠ 0 := by
  rcases Finset.mem_image.mp hp with ⟨P, hP, rfl⟩
  have hPne : P ≠ ⊥ := by
    have hI : differentIdeal ℤ (𝓞 (T.arithmetic.F)) ≠ ⊥ := differentIdeal_ne_bot
    have hmemP : P ∈ UniqueFactorizationMonoid.primeFactors
        (differentIdeal ℤ (𝓞 (T.arithmetic.F))) := by
      simpa [differentPlaces] using hP
    have hmem : P ∈ UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (𝓞 (T.arithmetic.F))) :=
      UniqueFactorizationMonoid.mem_primeFactors.mp hmemP
    have hdiv : P ∣ differentIdeal ℤ (𝓞 (T.arithmetic.F)) :=
      (mem_normalizedFactors_iff hI).mp hmem |>.2
    have hle : differentIdeal ℤ (𝓞 (T.arithmetic.F)) ≤ P :=
      Ideal.dvd_iff_le.mp hdiv
    intro hbot
    exact hI (le_antisymm (hbot ▸ hle) bot_le)
  have hge : (1 : ℝ) ≤ ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ) :=
    underIntGen_natAbs_ge_one T hPne
  have hpos : 0 < (underIntGen (K := T.arithmetic.F) P).natAbs := by
    exact_mod_cast hge
  exact Nat.pos_iff_ne_zero.mp hpos

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity3Actual
end