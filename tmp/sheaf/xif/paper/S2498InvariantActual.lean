import tmp.sheaf.xif.paper.S2497InvariantActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual
import tmp.sheaf.xif.paper.S2470SignActionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S2497InvariantActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
open LeanFormal.IUT.XiFPaper.S2470SignActionActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2498InvariantActual

noncomputable def S2498Invariant :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp S2470SignAction.inversion S2496Map)
      S2496Map := by
  let eta := Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (F := F) S2482AffineInvolution)
    (S1742StrongTransOfHom (F := F) S2496f)
  have hhom : S1742HomOfStrongTrans eta = S2496f := by
    dsimp [eta]
    rw [S2398HomOfStrongTrans_vcomp]
    exact S2497InvScheme
  have e : S1742StrongTransOfHom (F := F) (S1742HomOfStrongTrans eta) ≅ eta :=
    S1742StrongTransIsoOfHom eta
  rw [hhom] at e
  exact e.symm

#print axioms S2498Invariant

end LeanFormal.IUT.XiFPaper.S2498InvariantActual
end