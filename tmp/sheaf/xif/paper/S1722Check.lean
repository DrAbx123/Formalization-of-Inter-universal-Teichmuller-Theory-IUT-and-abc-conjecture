import tmp.sheaf.xif.paper.S1722DegreePrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

#check S1722DegreePrimeToL
#check S1722_finrank_dvd_96
#check S1722_finrank_prime_factors_le_three
#check S1722InitialThetaArithmeticData

example (l : PrimeGeFive) : S1720DegreePrimeToL l := S1722DegreePrimeToL l
