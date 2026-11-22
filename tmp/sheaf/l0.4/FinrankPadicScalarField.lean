import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativePadicDegrees
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Finrank of the normalized completion over the p-adic scalar field

The concrete Gaussian place has relative completion degree one and its lower
rational completion is one-dimensional over `ℚ_[5]`; the common-prime tower
then gives finrank one over `PadicScalarField concretePlace`.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance finrankFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance finrankGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  Fact.mk (by
    apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
    intro b hb
    have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb] at hnonneg
    exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg)

theorem concretePlace_finrank_padicScalarField_eq_one :
    Module.finrank (PadicScalarField concretePlace)
      (NormalizedCompletion concretePlace) = 1 := by
  let P : FinitePlaceAtPrime GaussianField 5 :=
    ⟨concretePlace, concretePlace_rationalPrime_eq_five⟩
  have hrat :
      Module.finrank ℚ_[5]
        (CommonPrimeCompletion (relativeCommonPrimePlace (k := ℚ) P)) = 1 :=
    finrank_commonPrimeCompletion_rat_of_prime 5
      (relativeCommonPrimePlace (k := ℚ) P)
  have hdeg : relativeCompletionDegree (k := ℚ) P.val = 1 :=
    concreteGaussianFivePlace_relativeCompletionDegree_eq_one
  have htower := finrank_commonPrimeCompletion_tower (k := ℚ) P
  have hone : Module.finrank ℚ_[5] (CommonPrimeCompletion P) = 1 := by
    rw [← htower, hrat, hdeg, one_mul]
  have hprimes : completionRationalPrime concretePlace = ⟨5, Nat.prime_five⟩ :=
    Subtype.ext concretePlace_rationalPrime_eq_five
  rw [hprimes]
  simpa [P, CommonPrimeCompletion, NormalizedCompletion] using hone
end LeanFormal.IUT.IUTII.Frobenioid.Example36

end