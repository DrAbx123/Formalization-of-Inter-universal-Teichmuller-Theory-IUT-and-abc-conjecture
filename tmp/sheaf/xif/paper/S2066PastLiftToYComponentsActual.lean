import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2066: explicit hom/inv components of pastLiftToY

S2058's `pastLiftToY` is a nested `Iso.trans`/`Iso.symm`.  For the
`liftTwoCell_toY` distribution we need its hom and inv 2-cells explicitly,
without unfolding nested `Iso.trans` by `simp`; the lemmas below rewrite only
`Iso.trans_hom`, `Iso.trans_inv`, `Iso.symm_hom`, `Iso.symm_inv`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2066PastLiftToYComponentsActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual

universe u
variable {F : Type u} [Field F]
variable {D : S2058Pasting (F := F)}

/-- The explicit hom 2-cell of `pastLiftToY`. -/
theorem S2066_pastLiftToY_hom
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastLiftToY w1 w2 cone).hom =
      (S2058AssociatorIso (D.pastLift w1 w2 cone) D.toY1 D.toY2).inv ≫
        (S2058WhiskerRight (w1.liftToY W (D.pastCone1 w2 cone)) D.toY2).hom ≫
          ((w2.liftToY W (D.pastCone2 cone) :
            Iso ((D.pastCone1 w2 cone).toY.vcomp D.toY2) cone.toY)).hom := by
  rw [S2058Pasting.pastLiftToY]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]

/-- The explicit inv 2-cell of `pastLiftToY`. -/
theorem S2066_pastLiftToY_inv
    (w1 : D.square1.TwoPullbackWitness) (w2 : D.square2.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F} (cone : D.squareP.Cone W) :
    (D.pastLiftToY w1 w2 cone).inv =
      ((w2.liftToY W (D.pastCone2 cone) :
        Iso ((D.pastCone1 w2 cone).toY.vcomp D.toY2) cone.toY)).inv ≫
        (S2058WhiskerRight (w1.liftToY W (D.pastCone1 w2 cone)) D.toY2).inv ≫
          (S2058AssociatorIso (D.pastLift w1 w2 cone) D.toY1 D.toY2).hom := by
  rw [S2058Pasting.pastLiftToY]
  rw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc]

#print axioms S2066_pastLiftToY_hom
#print axioms S2066_pastLiftToY_inv

end LeanFormal.IUT.XiFPaper.S2066PastLiftToYComponentsActual

end
