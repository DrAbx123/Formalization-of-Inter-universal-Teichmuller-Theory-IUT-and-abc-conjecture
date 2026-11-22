import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels

/-!
# Mzk1PrimeLabelConsumerActual — consumer theorems over the prime label/PrimeGeFive assets
(tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeLabelConsumerActual

open LeanFormal.IUT

/-- Consumer: the label value is prime. -/
theorem consumer_prime (l : PrimeGeFive) : Nat.Prime l.value :=
  l.prime

/-- Consumer: the label value is at least five. -/
theorem consumer_ge_five (l : PrimeGeFive) : 5 ≤ l.value :=
  l.ge_five

/-- Consumer: the label value is not two. -/
theorem consumer_ne_two (l : PrimeGeFive) : l.value ≠ 2 :=
  l.ne_two

/-- Consumer: the label value is odd. -/
theorem consumer_odd (l : PrimeGeFive) : Odd l.value :=
  l.odd

/-- Consumer: the label value has a Fact instance. -/
theorem consumer_factPrime (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

#check consumer_prime
#check consumer_ge_five
#check consumer_ne_two
#check consumer_odd
#check consumer_factPrime

end LeanFormal.IUT.XiFPaper.Mzk1PrimeLabelConsumerActual
end
