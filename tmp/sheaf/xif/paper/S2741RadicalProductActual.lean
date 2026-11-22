import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport
import LeanFormal.IUT.Foundations.Arithmetic.Radical

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2741RadicalProductActual

/-- The product of the primes in the arithmetic prime support of the actual
ABC point `a/c` is the radical of `a*b*c`. -/
theorem S2741_prod_support_eq_radical_abc {a b c : Nat}
    (h : IsABCTriple a b c) :
    (∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p) =
      natRadical (a * b * c) := by
  rw [arithmeticPrimeSupport_abcRationalPoint h, ← natRadical_eq_prod_primeFactors]

/-- The same support product is at least the radical of `a*c`, since
`a*c ∣ a*b*c`. -/
theorem S2741_prod_support_ge_radical_ac {a b c : Nat}
    (h : IsABCTriple a b c) :
    natRadical (a * c) ≤
      ∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p := by
  rw [S2741_prod_support_eq_radical_abc h]
  have hdvd : a * c ∣ a * b * c := ⟨b, by ring⟩
  have hne : a * b * c ≠ 0 := by
    rcases h with ⟨ha, hb, hsum, _⟩
    have hcpos : 0 < c := by omega
    exact Nat.mul_ne_zero (Nat.mul_ne_zero ha.ne' hb.ne') hcpos.ne'
  exact Nat.le_of_dvd (natRadical_pos (a * b * c))
    (natRadical_dvd_radical_of_dvd hdvd hne)

#check S2741_prod_support_eq_radical_abc
#check S2741_prod_support_ge_radical_ac
#print axioms S2741_prod_support_ge_radical_ac

end LeanFormal.IUT.XiFPaper.S2741RadicalProductActual
end
