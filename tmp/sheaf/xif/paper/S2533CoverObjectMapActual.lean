import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2533CoverObjectMapActual

noncomputable def S2533ObjectMap (A : CommAlgCat.FiniteEtale F) :
    Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  S2517InvObj
    ((FiniteEtaleCover.pullback (S := Spec (CommRingCat.of F))
      (T := S2482AffineScheme) S2482AffineOver.hom).obj
      (finiteEtaleAlgebraCover F A))

#check S2533ObjectMap
#print axioms S2533ObjectMap
end LeanFormal.IUT.XiFPaper.S2533CoverObjectMapActual
end