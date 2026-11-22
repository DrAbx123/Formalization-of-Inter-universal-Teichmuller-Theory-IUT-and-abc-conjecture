import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S2495cFUnconditionalActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2511CoverCategoryActual

noncomputable instance S2511CoverCategory :
    Category.{1, 1} (Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :=
  S1728CoverCategory11 (F := F) (X := S2482Orbicurve)

noncomputable instance S2511CoverCategoryCF :
    Category.{1, 1} (Iut.OrbicurveFiniteEtaleCover S2495cF) :=
  S1728CoverCategory11 (F := F) (X := S2495cF)

end LeanFormal.IUT.XiFPaper.S2511CoverCategoryActual
end