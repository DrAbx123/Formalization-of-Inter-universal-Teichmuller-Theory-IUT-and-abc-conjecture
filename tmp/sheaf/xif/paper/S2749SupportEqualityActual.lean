import tmp.sheaf.xif.paper.S2741RadicalProductActual
import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2741RadicalProductActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual

/-- Exact support equality for the ABC rational point: the arithmetic prime
support of `a/c` is the prime-factor set of `a*b*c`. -/
theorem S2749_support_eq_primeFactors {a b c : Nat} (h : IsABCTriple a b c) :
    arithmeticPrimeSupport (abcRationalPoint a c) = (a * b * c).primeFactors :=
  arithmeticPrimeSupport_abcRationalPoint h

theorem S2749_mem_support_iff {a b c : Nat} (h : IsABCTriple a b c)
    (p : Nat) :
    p ∈ arithmeticPrimeSupport (abcRationalPoint a c) ↔
      p ∈ (a * b * c).primeFactors := by
  rw [S2749_support_eq_primeFactors h]

/-- Product of the support primes is exactly the radical of `a*b*c`. -/
theorem S2749_prod_support_eq_radical {a b c : Nat} (h : IsABCTriple a b c) :
    (∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p) =
      natRadical (a * b * c) :=
  S2741_prod_support_eq_radical_abc h

/-- The support-index subtype has cardinality equal to the prime-factor set
cardinality; this is a direct support count, not the S2735 count. -/
theorem S2749_supportIndex_card {a b c : Nat} (h : IsABCTriple a b c) :
    Fintype.card (SupportIndex (abcRationalPoint a c)) =
      (a * b * c).primeFactors.card := by
  rw [Fintype.card_coe]
  rw [S2749_support_eq_primeFactors h]

#check S2749_support_eq_primeFactors
#check S2749_mem_support_iff
#check S2749_prod_support_eq_radical
#check S2749_supportIndex_card
#print axioms S2749_supportIndex_card

end LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
end
