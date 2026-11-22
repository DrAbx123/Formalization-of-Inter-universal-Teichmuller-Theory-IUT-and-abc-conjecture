import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Rational-unit valuation at the Gaussian five-place

The originally proposed statement `∀ x : ℚˣ, v(algebraMap x) = 1` is false:
`5 : ℚˣ` is a unit of the field but has 5-adic valuation `exp (-1)`, so its
Gaussian-place value is not 1.  This file records the exact proposed statement
as a `Prop` definition and the correct conditional pointwise bridge.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance rationalUnitFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance rationalUnitGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  Fact.mk (by
    apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
    intro b hb
    have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb] at hnonneg
    exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg)

/-- The exact statement proposed for stage 3 (unconditional over `ℚˣ`). -/
def proposedRationalUnitValuationStatement : Prop :=
  ∀ x : ℚˣ,
    (IsDedekindDomain.HeightOneSpectrum.valuation GaussianField
      concreteGaussianFivePlace.maximalIdeal)
      (algebraMap ℚ GaussianField (x : ℚ)) = 1

/-- Correct conditional form: a rational number with 5-adic value `1` has
Gaussian value `1`. -/
theorem concreteGaussianFivePlace_valuation_eq_one_of_rat_eq_one
    (x : ℚ)
    (hx : (IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal) x = 1) :
    (IsDedekindDomain.HeightOneSpectrum.valuation GaussianField
      concreteGaussianFivePlace.maximalIdeal)
      (algebraMap ℚ GaussianField x) = 1 :=
  (concreteGaussianFivePlace_valuation_eq_one_iff x).mp hx

end LeanFormal.IUT.IUTII.Frobenioid.Example36

end
