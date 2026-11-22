import tmp.sheaf.xif.paper.S1896BoundaryCuspActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
open scoped Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.S2537RepresentableModificationActual

variable {F : Type} [Field F]

theorem S2537Modification_subsingleton
    {A : Iut.EtaleStackPseudofunctor F} (S : Iut.SchemeOverField F)
    {f g : Pseudofunctor.StrongTrans A (S1742YS (F := F) S)}
    (alpha beta : f ⟶ g) : alpha = beta :=
  S1896Modification_subsingleton (F := F) S alpha beta

#check S2537Modification_subsingleton
#print axioms S2537Modification_subsingleton
end LeanFormal.IUT.XiFPaper.S2537RepresentableModificationActual
end