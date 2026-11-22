import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe30

#check @MorphismProperty.CostructuredArrow.isoMk
#check @CategoryTheory.CostructuredArrow.isoMk
#check @CommAlgCat.FiniteEtale.of
#check @CommAlgCat.FiniteEtale_coe
#check @RingHom.toAlgebra_algebraMap
#check @RingHom.algebraMap_toAlgebra
#check @Algebra.algebraMap_eq_ofRingHom
#check @RingHom.toAlgebra
#check @Algebra.ofId
#check @AlgHom.toRingHom_injective
#check @AlgHom.ext
#check @RingHom.toRingHom_inj

end Probe30
