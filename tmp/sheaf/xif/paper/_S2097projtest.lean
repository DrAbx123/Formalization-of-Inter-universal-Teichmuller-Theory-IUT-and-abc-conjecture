import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual
noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
namespace Test2097
universe u
example {P X Y Z : EtaleStackPseudofunctor S1726K}
    (toX : Pseudofunctor.StrongTrans P X) (toY : Pseudofunctor.StrongTrans P Y)
    (x : Pseudofunctor.StrongTrans X Z) (y : Pseudofunctor.StrongTrans Y Z)
    (c : Iso (Pseudofunctor.StrongTrans.vcomp toX x) (Pseudofunctor.StrongTrans.vcomp toY y))
    {W : EtaleStackPseudofunctor S1726K} (L : Pseudofunctor.StrongTrans W P)
    (T : Pseudofunctor.StrongTrans W Y)
    (h : Iso (Pseudofunctor.StrongTrans.vcomp L (EtalePseudofunctorSquare.mk toX toY x y c).toY) T) :
    Iso (Pseudofunctor.StrongTrans.vcomp L toY) T := h
end Test2097
end