import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual
import tmp.sheaf.xif.paper.S2482CorrectedUniquenessAlgActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482TwoYonedaBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open CategoryTheory

theorem S2482HomOfStrongTrans_ellipticInvolution :
    S1742HomOfStrongTrans S2482EllipticInvolution = S2482AffineInvolution := by
  exact S1742HomOfStrongTrans_strongTransOfHom (F := F) S2482AffineInvolution

theorem S2482TwoIso_of_hom_eq
    (eta : S2482Orbicurve.Hom S2482Orbicurve)
    (h : S1742HomOfStrongTrans eta = S2482AffineInvolution) :
    Nonempty (Iso eta S2482EllipticInvolution) := by
  have e := S1742StrongTransIsoOfHom (F := F) eta
  refine ⟨?_⟩
  change @Iso
    (Pseudofunctor.StrongTrans (S1742YS S2482AffineOver) (S1742YS S2482AffineOver))
    ((S1742YS S2482AffineOver).homCategory (S1742YS S2482AffineOver))
    eta (S1742StrongTransOfHom S2482AffineInvolution)
  simpa [h] using e.symm


end LeanFormal.IUT.XiFPaper.S2482TwoYonedaBridgeActual
end