import tmp.sheaf.xif.paper.S2497InvariantSchemeActual
import tmp.sheaf.xif.paper.S2470SignActionActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S2497InvariantSchemeActual
open LeanFormal.IUT.XiFPaper.S2470SignActionActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2498InvariantStrongTransActual

noncomputable def S2498Invariant :
    Iso (Pseudofunctor.StrongTrans.vcomp
      S2470SignAction.inversion S2496Map) S2496Map := by
  let eta := Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (F := F) S2482AffineInvolution)
    (S1742StrongTransOfHom (F := F) S2496f)
  have h : S1742HomOfStrongTrans eta = S2496f := by
    dsimp [eta]
    rw [S2398HomOfStrongTrans_vcomp]
    exact S2497InvScheme
  let e := S1742StrongTransIsoOfHom (F := F) eta
  rw [h] at e
  exact e.symm

#check S2498Invariant
#print axioms S2498Invariant

end LeanFormal.IUT.XiFPaper.S2498InvariantStrongTransActual
end
