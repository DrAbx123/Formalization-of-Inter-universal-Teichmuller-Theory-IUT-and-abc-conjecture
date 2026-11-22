import tmp.sheaf.xif.paper.S2741RadicalProductActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm

noncomputable section
open scoped BigOperators nonZeroDivisors
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2741RadicalProductActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2742AbsNormRadicalConnectionActual

variable {K : Type*} [Field K] [NumberField K]

/-- If the arithmetic support product of `a/c` is bounded by `Ideal.absNorm J`,
then `natRadical (a*c)` is bounded by `Ideal.absNorm J`.  This composes the
actual S2741 support-product lower bound with the S2739 absNorm lower bound. -/
theorem S2742_radical_ac_le_absNorm_of_prod_le
    {a b c : Nat} (h : IsABCTriple a b c)
    (J : Ideal (NumberField.RingOfIntegers K))
    (hprod :
      (∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p) ≤
        Ideal.absNorm J) :
    natRadical (a * c) ≤ Ideal.absNorm J := by
  exact le_trans (S2741_prod_support_ge_radical_ac h) hprod

/-- Fractional-ideal version: if the support product (as a rational number)
is bounded by `FractionalIdeal.absNorm J`, then its radical is bounded too. -/
theorem S2742_radical_ac_le_fractionalAbsNorm_of_prod_le
    {R : Type*} [CommRing R] [IsDomain R] {L : Type*} [Field L]
    [Algebra R L] [IsFractionRing R L] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    {a b c : Nat} (h : IsABCTriple a b c)
    (J : FractionalIdeal R⁰ L)
    (hprod :
      ((∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p : ℕ) : ℚ) ≤
        FractionalIdeal.absNorm J) :
    (natRadical (a * c) : ℚ) ≤ FractionalIdeal.absNorm J :=
  le_trans (by exact_mod_cast S2741_prod_support_ge_radical_ac h) hprod

#check S2742_radical_ac_le_absNorm_of_prod_le
#check S2742_radical_ac_le_fractionalAbsNorm_of_prod_le
#print axioms S2742_radical_ac_le_absNorm_of_prod_le

end LeanFormal.IUT.XiFPaper.S2742AbsNormRadicalConnectionActual
end
