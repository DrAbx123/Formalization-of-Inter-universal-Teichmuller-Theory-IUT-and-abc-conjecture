import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2519InvFunctorActual
import tmp.sheaf.xif.paper.S2519InvEquivalenceGoalActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2551Probe

#check S1742StrongTransIsoOfHom
#check Pseudofunctor.StrongTrans.ext
#check Pseudofunctor.StrongTrans.isoMk
#check CategoryTheory.Iso.ext
#check CategoryTheory.NatTrans.ext
#check S2519BasePoint
#check S2482Orbicurve
#check Pseudofunctor.StrongTrans.leftUnitor
#check Pseudofunctor.StrongTrans.rightUnitor
#check Pseudofunctor.StrongTrans.associator
#check S1641CoverMapId
#check S1641CoverMapComp
#check S1728CoverMapRel
#check S1728CoverCategory11
#check S2519PreimageCover
#check S2519InvFunctorEssSurjGoal

end LeanFormal.IUT.XiFPaper.S2551Probe
