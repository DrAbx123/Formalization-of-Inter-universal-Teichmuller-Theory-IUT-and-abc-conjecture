import tmp.sheaf.xif.paper.S1819G3IntegratedActual

open CategoryTheory CategoryTheory.Limits

namespace S1819Check

variable {K : Type} [Field K]

example : S1786.MonoInducesIsoOnDirectSummandField K :=
  S1819.monoInducesIsoOnDirectSummandField (K := K)

example : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
  S1819.monoInducesIsoOnDirectSummandField_S1793 (K := K)

example : PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1819.preGaloisCategory (K := K)

example : PreGaloisCategory (S1786.FiniteEtaleAlg K) :=
  S1819.preGaloisCategory (K := K)

#check @S1819.monoInducesIsoOnDirectSummandField
#check @S1819.preGaloisCategory
#print axioms S1819.monoInducesIsoOnDirectSummandField
#print axioms S1819.preGaloisCategory

end S1819Check
