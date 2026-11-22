import tmp.sheaf.xif.paper.S2066PastLiftToYComponentsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2066PastLiftToYComponentsActual

namespace Probe
universe u
variable {F : Type u} [Field F]
variable {D : S2058Pasting (F := F)}

example (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastLiftToY w1 w2 cone).hom =
      (S2058AssociatorIso (D.pastLift w1 w2 cone) D.toY1 D.toY2).inv ≫
        (S2058WhiskerRight (w1.liftToY W (D.pastCone1 w2 cone)) D.toY2).hom ≫
          ((w2.liftToY W (D.pastCone2 cone) :
            Iso ((D.pastCone1 w2 cone).toY.vcomp D.toY2) cone.toY)).hom :=
  S2066_pastLiftToY_hom w1 w2 cone

example {A B C : EtaleStackPseudofunctor F}
    {f f' : Pseudofunctor.StrongTrans A B} (e : Iso f f') (g : Pseudofunctor.StrongTrans B C) :
    (S2058WhiskerRight e g).hom = Bicategory.whiskerRight e.hom g := rfl

example {A B C E : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C E) :
    (S2058AssociatorIso f g h).hom = (Bicategory.associator f g h).hom := rfl

example {A B C E : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C E) :
    (S2058AssociatorIso f g h).inv = (Bicategory.associator f g h).inv := rfl

example (w2 : D.square2.TwoPullbackWitness) {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone1 w2 cone).commutes = (w2.liftToX W (D.pastCone2 cone)).symm := rfl

example (w2 : D.square2.TwoPullbackWitness) {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone1 w2 cone).toX = cone.toX := rfl

example (w2 : D.square2.TwoPullbackWitness) {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastCone1 w2 cone).toY = w2.lift W (D.pastCone2 cone) := rfl

example (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    D.pastLift w1 w2 cone = w1.lift W (D.pastCone1 w2 cone) := rfl

-- square projections
example : D.squareP.toX = D.toX1 := rfl
example : D.squareP.toY = Pseudofunctor.StrongTrans.vcomp D.toY1 D.toY2 := rfl
example : D.square1.toX = D.toX1 := rfl
example : D.square1.toY = D.toY1 := rfl
example : D.square2.toX = D.xi := rfl
example : D.square2.toY = D.toY2 := rfl

#check @Bicategory.whiskerRight_comp
#check @Bicategory.comp_whiskerRight
#check @Bicategory.whisker_exchange
#check @Bicategory.associator_naturality_left
#check @CategoryTheory.cancel_epi
#check @CategoryTheory.cancel_mono
#check @Bicategory.whiskerLeft_inv_hom
#check @Bicategory.whiskerLeft_hom_inv
#check @Iso.inv_hom_id_assoc
#check @Iso.hom_inv_id_assoc
#check @Pseudofunctor.StrongTrans.whiskerRight
#check @Pseudofunctor.StrongTrans.whiskerLeft
#check @CategoryTheory.Pseudofunctor.StrongTrans.homCategory
#check @Pseudofunctor.StrongTrans.homCategory.ext

end Probe
