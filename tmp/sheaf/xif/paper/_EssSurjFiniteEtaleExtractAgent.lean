import tmp.sheaf.xif.paper.S2547TransportIsoActual
import tmp.sheaf.xif.paper.S2517RepresentableFiniteEtaleActual
import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportIsoActual
open LeanFormal.IUT.XiFPaper.S2542TransportE1E4Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.EssSurjFiniteEtaleExtractAgent

variable (S : Iut.SchemeOverField F)
variable (f : Iut.EtaleStackOverField.Hom (S2517TStack S) S2482Orbicurve.stack)

#check S1742HomOfStrongTrans (F := F) f
#check S1742StrongTransIsoOfHom (F := F) f
#check Iut.EtaleStackFiniteEtaleMorphism f

example : S ⟶ S2482AffineOver := S1742HomOfStrongTrans (F := F) f

variable (hf : Iut.EtaleStackFiniteEtaleMorphism f)

#check hf.baseChange S2482AffineOver (S1742StrongTransOfHom (F := F) (𝟙 S2482AffineOver))

end LeanFormal.IUT.XiFPaper.EssSurjFiniteEtaleExtractAgent
end
