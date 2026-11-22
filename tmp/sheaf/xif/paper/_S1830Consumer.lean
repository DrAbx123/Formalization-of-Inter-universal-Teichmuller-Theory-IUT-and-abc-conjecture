import tmp.sheaf.xif.paper.S1830G2G3RPrimeActual
import tmp.sheaf.xif.paper.S1825GaloisOnSmallCategoryActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1825GaloisOnSmallCategoryActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual

attribute [local instance] S1809CoverCategory01

namespace S1830Consumer

/-- S1825 named residual is discharged. -/
theorem algPreGaloisMissing : S1825AlgPreGaloisMissing :=
  S1830Main.S1830AlgPreGaloisMissing

/-- The unconditional algebra-side pre-Galois category. -/
theorem preGalois : PreGaloisCategory S1779AlgR :=
  S1830Main.S1830PreGaloisCategory

/-- S1825 consumption: the actual pre-Galois structure on the small cover category
from the affine equivalence and the now-unconditional algebra-side data. -/
theorem coverPreGalois (e : S1825AffineEquiv) : PreGaloisCategory S1728Cover :=
  S1825PreGaloisCategory_of_missing e S1830Main.S1830AlgPreGaloisMissing

end S1830Consumer

#print axioms S1830Consumer.algPreGaloisMissing
#print axioms S1830Consumer.preGalois
#print axioms S1830Consumer.coverPreGalois
