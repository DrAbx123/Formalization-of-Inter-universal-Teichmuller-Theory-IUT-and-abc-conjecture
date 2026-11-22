import tmp.sheaf.xif.paper.S1723DegreeBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1723DegreeBoundActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

#check S1723_finrank_dvd_96
#check S1723_finrank_prime_factors_le_three
#check S1723DegreePrimeToL

/-- The exact target of the task, restated by the checker. -/
example : Module.finrank ℚ S1720Field ∣ 96 := S1723_finrank_dvd_96

/-- The exact unconditional degreePrimeToL statement consumed by S1720. -/
example (l : PrimeGeFive) : Nat.Coprime (Module.finrank ℚ S1720Field) l.value :=
  S1723DegreePrimeToL l

#print axioms S1723_finrank_dvd_96
#print axioms S1723DegreePrimeToL
