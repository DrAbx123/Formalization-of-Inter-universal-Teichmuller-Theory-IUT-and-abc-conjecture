import tmp.sheaf.xif.paper.S2005FprimeGroupActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2615DegreeTwelvePrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The actual degree of the paper field: `[F' : Q] = 12` (S2005). -/
theorem S2615_finrank : Module.finrank ℚ S1720Field = 12 :=
  S2005_finrank

/-- `12` is coprime to every prime `l ≥ 5`. -/
theorem coprime_twelve_primeGeFive (l : PrimeGeFive) :
    Nat.Coprime 12 l.value := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd l.prime]
  intro hdiv
  have hle : l.value ≤ 12 := Nat.le_of_dvd (by norm_num) hdiv
  have h5 : 5 ≤ l.value := l.ge_five
  have hprime := l.prime
  interval_cases l.value
  · norm_num at hdiv
  · norm_num at hprime
  · norm_num at hdiv
  · norm_num at hprime
  · norm_num at hprime
  · norm_num at hprime
  · norm_num at hdiv
  · norm_num at hprime

/-- Unconditional `S1720DegreePrimeToL` from the actual degree `12`. -/
theorem S2615DegreePrimeToL (l : PrimeGeFive) : S1720DegreePrimeToL l := by
  unfold S1720DegreePrimeToL
  rw [S2615_finrank]
  exact coprime_twelve_primeGeFive l

#print axioms S2615_finrank
#print axioms S2615DegreePrimeToL

end LeanFormal.IUT.XiFPaper.S2615DegreeTwelvePrimeActual
end
