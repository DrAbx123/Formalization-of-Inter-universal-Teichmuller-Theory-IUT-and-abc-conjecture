import tmp.sheaf.xif.paper.S2064PasteLiftActual

/-! # S2065: remaining block of the corrected pasting witness

Adopts S2064's corrected datum `S2064PasteProblem`.  The first block
(lift/liftToX/liftToY) is already constructed there.  This file packages the
four remaining fields of the pasted `TwoPullbackWitness` as one structure and
assembles the full witness from the first block plus that structure.

The four fields are exactly:
* liftTwoCell;
* liftTwoCell_toX;
* liftTwoCell_toY;
* twoCell_ext.

No field is fabricated: the structure has no inhabitant and no `sorry`/axiom
is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2065PasteRemainingBlockActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2064PasteLiftActual

universe u
variable {F : Type u} [Field F]

namespace S2064PasteProblem

variable (p : S2064PasteProblem (F := F))

/-- The four remaining fields of the full pasted `TwoPullbackWitness`. -/
structure S2065RemainingBlock where
  liftTwoCell : ∀ (W' : EtaleStackPseudofunctor F)
    (source target : p.composite.Cone W'),
    p.composite.ConeMorphism source target →
      p.lift source ⟶ p.lift target
  liftTwoCell_toX : ∀ (W' : EtaleStackPseudofunctor F)
    (source target : p.composite.Cone W')
    (morphism : p.composite.ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight
        (liftTwoCell W' source target morphism) p.composite.toX =
      (p.liftToX source).hom ≫ morphism.toX ≫ (p.liftToX target).inv
  liftTwoCell_toY : ∀ (W' : EtaleStackPseudofunctor F)
    (source target : p.composite.Cone W')
    (morphism : p.composite.ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight
        (liftTwoCell W' source target morphism) p.composite.toY =
      (p.liftToY source).hom ≫ morphism.toY ≫ (p.liftToY target).inv
  twoCell_ext : ∀ (W' : EtaleStackPseudofunctor F)
    {first second : Pseudofunctor.StrongTrans W' p.P2}
    (alpha beta : first ⟶ second),
    Pseudofunctor.StrongTrans.whiskerRight alpha p.composite.toX =
        Pseudofunctor.StrongTrans.whiskerRight beta p.composite.toX →
      Pseudofunctor.StrongTrans.whiskerRight alpha p.composite.toY =
          Pseudofunctor.StrongTrans.whiskerRight beta p.composite.toY →
        alpha = beta

/-- The full witness from the S2064 first block and the remaining block. -/
noncomputable def S2065TwoPullbackWitnessOfRemaining
    (R : p.S2065RemainingBlock) :
    EtalePseudofunctorSquare.TwoPullbackWitness p.composite where
  lift := fun W' cone => p.lift cone
  liftToX := fun W' cone => p.liftToX cone
  liftToY := fun W' cone => p.liftToY cone
  liftTwoCell := R.liftTwoCell
  liftTwoCell_toX := R.liftTwoCell_toX
  liftTwoCell_toY := R.liftTwoCell_toY
  twoCell_ext := R.twoCell_ext

end S2064PasteProblem

#check S2064PasteProblem.S2065RemainingBlock
#check S2064PasteProblem.S2065TwoPullbackWitnessOfRemaining

end LeanFormal.IUT.XiFPaper.S2065PasteRemainingBlockActual

end
