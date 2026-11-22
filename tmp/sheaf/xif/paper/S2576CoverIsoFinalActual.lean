import tmp.sheaf.xif.paper.S2575CoverIsoActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual
open LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual
open LeanFormal.IUT.XiFPaper.S2569CoverMapActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual

theorem S2576_cast_inv_cancel
    {P Q : Iut.EtaleStackPseudofunctor S2480QiActual.F}
    (h : P = Q) (L : Pseudofunctor.StrongTrans P S2482Orbicurve.stack.fiber) :
    castStrongTrans h.symm (castStrongTrans h L) = L := by
  rw [← castStrongTrans_trans h h.symm L]
  have hh : h.trans h.symm = rfl := Subsingleton.elim _ _
  rw [hh, castStrongTrans_rfl]

noncomputable def S2576_castIso
    {P Q : Iut.EtaleStackPseudofunctor S2480QiActual.F}
    (h : P = Q)
    {L1 L2 : Pseudofunctor.StrongTrans P S2482Orbicurve.stack.fiber}
    (e : Iso L1 L2) :
    Iso (castStrongTrans h L1) (castStrongTrans h L2) := by
  cases h
  exact e

#check S2576_cast_inv_cancel
#check S2576_castIso
end LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual
end
