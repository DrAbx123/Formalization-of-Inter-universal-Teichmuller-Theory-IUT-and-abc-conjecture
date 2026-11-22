import tmp.sheaf.xif.paper.S2050TwoPullbackPasteGapActual

/-!
# S2064: the first block of the two-pullback pasting witness

## Verdict on the literal S2050 statement

S2050 fixes the target statement and the coherence list for
TwoPullbackWitness.paste, but its S2050PasteProblem supplies the composite
square as *independent* data.  In particular the base object Z of the
composite square has no recorded relation to the base object Y of sq1, and
the base legs composite.xToBase, composite.yToBase have no recorded relation
to sq1.xToBase, sq1.yToBase.  A cone over the composite square therefore
carries a 2-isomorphism over Z, while the cone over sq1 required by w1.lift
needs a 2-isomorphism over Y.  Neither w1 nor w2 can manufacture the missing
comparison, so the literal S2050PasteProblem.lift is not definable from the
recorded fields.  The exact first missing datum is the pasting identification
of the composite square with the square obtained by composing sq2 after sq1
(in particular Z = Y and the two shared base legs agree).  It is not a missing
Mathlib 2-category lemma: Bicategory.associator, Bicategory.whiskerLeftIso and
Bicategory.whiskerRightIso are available and are used below.

## What is implemented here

S2064PasteProblem is the corrected pasting datum.  The second square
S2064SecondSquare has its base legs tied to sq1, and the composite square is
*defined* as the pasted square, not supplied independently.  For this datum
the first block of a TwoPullbackWitness is constructed:

* S2064PasteProblem.composite: the pasted square, whose commutes 2-isomorphism
  is built from sq2.commutes and the associator;
* cone1 and cone2: the two dependent cone lifts, first through w1.lift (giving
  W' -> P1) and then through w2.lift;
* lift, liftToX, liftToY: the first three fields of a TwoPullbackWitness,
  with the comparisons built from w1.liftToY, w2.liftToX, w2.liftToY, the
  associator and right whiskering.

S2064PasteProblem.toS2050 records the same datum as an S2050PasteProblem whose
composite square is the actual pasted square, and
S2064PasteProblem.toS2050FirstBlock gives the first block for it.

The remaining fields of the full witness (liftTwoCell, liftTwoCell_toX,
liftTwoCell_toY and twoCell_ext) are not constructed here.  No sorry, no new
axiom, no fake witness and no Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S2064PasteLiftActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S2050TwoPullbackPasteGapActual

universe u
variable {F : Type u} [Field F]

/-! ## 1. Bicategory isomorphisms in the shapes used below -/

/-- The associator of three composable strong transformations. -/
noncomputable def S2064AssociatorIso
    {A B C D : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) :=
  Bicategory.associator (B := EtaleStackPseudofunctor F) f g h

/-- Right whiskering of a 2-isomorphism by a strong transformation. -/
noncomputable def S2064WhiskerRightIso
    {A B C : EtaleStackPseudofunctor F}
    {f f' : Pseudofunctor.StrongTrans A B} (e : Iso f f')
    (g : Pseudofunctor.StrongTrans B C) :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f' g) :=
  Bicategory.whiskerRightIso (B := EtaleStackPseudofunctor F) e g

/-! ## 2. The second square with its base legs tied to the first square -/

/-- The data of the second square.  Its two base legs are the first square's
base leg and the composite of the first square's two vertical legs, so that
the two squares are composable in the pasting sense. -/
structure S2064SecondSquare {P1 W S Y : EtaleStackPseudofunctor F}
    (P2 : EtaleStackPseudofunctor F) (sq1 : EtalePseudofunctorSquare P1 W S Y) where
  toX : Pseudofunctor.StrongTrans P2 W
  toY : Pseudofunctor.StrongTrans P2 P1
  commutes : Iso
    (Pseudofunctor.StrongTrans.vcomp toX sq1.xToBase)
    (Pseudofunctor.StrongTrans.vcomp toY
      (Pseudofunctor.StrongTrans.vcomp sq1.toY sq1.yToBase))

namespace S2064SecondSquare

variable {P1 W S Y P2 : EtaleStackPseudofunctor F}
variable {sq1 : EtalePseudofunctorSquare P1 W S Y}
variable (s : S2064SecondSquare P2 sq1)

/-- The second square as an ordinary two-commutative square. -/
noncomputable abbrev toSquare : EtalePseudofunctorSquare P2 W P1 Y where
  toX := s.toX
  toY := s.toY
  xToBase := sq1.xToBase
  yToBase := Pseudofunctor.StrongTrans.vcomp sq1.toY sq1.yToBase
  commutes := s.commutes

end S2064SecondSquare

/-! ## 3. The corrected pasting problem -/

/-- The pasting datum.  The second square shares the first square's base legs
and the composite square is the pasted square, not an independent square. -/
structure S2064PasteProblem where
  W : EtaleStackPseudofunctor F
  S : EtaleStackPseudofunctor F
  Y : EtaleStackPseudofunctor F
  P1 : EtaleStackPseudofunctor F
  P2 : EtaleStackPseudofunctor F
  sq1 : EtalePseudofunctorSquare P1 W S Y
  sq2 : S2064SecondSquare P2 sq1
  w1 : EtalePseudofunctorSquare.TwoPullbackWitness sq1
  w2 : EtalePseudofunctorSquare.TwoPullbackWitness sq2.toSquare

namespace S2064PasteProblem

variable (p : S2064PasteProblem (F := F))

/-- The composite square: apex P2, first leg sq2.toX, second leg
sq2.toY followed by sq1.toY, and the base legs of sq1. -/
noncomputable abbrev composite : EtalePseudofunctorSquare p.P2 p.W p.S p.Y where
  toX := p.sq2.toX
  toY := Pseudofunctor.StrongTrans.vcomp p.sq2.toY p.sq1.toY
  xToBase := p.sq1.xToBase
  yToBase := p.sq1.yToBase
  commutes := p.sq2.commutes.trans
    (S2064AssociatorIso p.sq2.toY p.sq1.toY p.sq1.yToBase).symm

/-- The cone over sq1 induced by a cone over the composite square. -/
noncomputable abbrev cone1 {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : p.sq1.Cone W' where
  toX := cone.toX
  toY := cone.toY
  commutes := cone.commutes

/-- The cone over sq2 induced by the composite cone and the first lift. -/
noncomputable abbrev cone2 {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : p.sq2.toSquare.Cone W' where
  toX := cone.toX
  toY := p.w1.lift W' (p.cone1 cone)
  commutes := by
    let h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp (p.w1.lift W' (p.cone1 cone))
          (Pseudofunctor.StrongTrans.vcomp p.sq1.toY p.sq1.yToBase))
        (Pseudofunctor.StrongTrans.vcomp cone.toY p.sq1.yToBase) :=
      (S2064AssociatorIso (p.w1.lift W' (p.cone1 cone))
        p.sq1.toY p.sq1.yToBase).symm.trans
        (S2064WhiskerRightIso (p.w1.liftToY W' (p.cone1 cone))
          p.sq1.yToBase)
    exact (p.cone1 cone).commutes.trans h2.symm

/-- The first step of the dependent cone lift: w1.lift gives a comparison
W' -> P1. -/
noncomputable abbrev liftToP1 {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : Pseudofunctor.StrongTrans W' p.P1 :=
  p.w1.lift W' (p.cone1 cone)

/-- The second step of the dependent cone lift: w2.lift gives W' -> P2. -/
noncomputable abbrev lift {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : Pseudofunctor.StrongTrans W' p.P2 :=
  p.w2.lift W' (p.cone2 cone)

/-- The comparison of the lift with the first composite leg. -/
noncomputable abbrev liftToX {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') :
    Iso (Pseudofunctor.StrongTrans.vcomp (p.lift cone) p.composite.toX) cone.toX :=
  p.w2.liftToX W' (p.cone2 cone)

/-- The comparison of the lift with the second composite leg, obtained by
combining w2.liftToY, w1.liftToY and the associator. -/
noncomputable abbrev liftToY {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') :
    Iso (Pseudofunctor.StrongTrans.vcomp (p.lift cone) p.composite.toY) cone.toY :=
  (S2064AssociatorIso (p.w2.lift W' (p.cone2 cone)) p.sq2.toY p.sq1.toY).symm.trans
    ((S2064WhiskerRightIso (p.w2.liftToY W' (p.cone2 cone)) p.sq1.toY).trans
      (p.w1.liftToY W' (p.cone1 cone)))

end S2064PasteProblem

/-! ## 4. The first three fields, packaged -/

/-- The first three fields of a TwoPullbackWitness, for any square. -/
structure S2064FirstBlock {P X Y Z : EtaleStackPseudofunctor F}
    (square : EtalePseudofunctorSquare P X Y Z) where
  lift : ∀ (W : EtaleStackPseudofunctor F), square.Cone W →
    Pseudofunctor.StrongTrans W P
  liftToX : ∀ (W : EtaleStackPseudofunctor F) (cone : square.Cone W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W cone) square.toX) cone.toX
  liftToY : ∀ (W : EtaleStackPseudofunctor F) (cone : square.Cone W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W cone) square.toY) cone.toY

namespace S2064PasteProblem

variable (p : S2064PasteProblem (F := F))

/-- The first block for the pasted square. -/
noncomputable abbrev firstBlock : S2064FirstBlock p.composite where
  lift := fun W' cone => p.lift cone
  liftToX := fun W' cone => p.liftToX cone
  liftToY := fun W' cone => p.liftToY cone

end S2064PasteProblem

/-- The Type-valued form of the first-block theorem. -/
def S2064PasteFirstBlockStatement : Type _ :=
  ∀ (p : S2064PasteProblem (F := F)), S2064FirstBlock p.composite

/-- The first block exists for every corrected pasting datum. -/
noncomputable def S2064PasteFirstBlockStatement_holds :
    S2064PasteFirstBlockStatement (F := F) :=
  fun p => p.firstBlock

/-! ## 5. Relation to the literal S2050PasteProblem -/

namespace S2064PasteProblem

variable (p : S2064PasteProblem (F := F))

/-- The corrected datum as an S2050PasteProblem whose composite square is the
actual pasted square. -/
noncomputable abbrev toS2050 : S2050PasteProblem (F := F) where
  W := p.W
  S := p.S
  Y := p.Y
  Z := p.Y
  P1 := p.P1
  P2 := p.P2
  sq1 := p.sq1
  sq2 := p.sq2.toSquare
  composite := p.composite
  w1 := p.w1
  w2 := p.w2

/-- The first block for the S2050 problem built from the corrected datum. -/
noncomputable abbrev toS2050FirstBlock :
    S2064FirstBlock p.toS2050.composite :=
  p.firstBlock

end S2064PasteProblem

/-! ## 6. Checks and axiom audit -/

#check S2064PasteProblem.lift
#check S2064PasteProblem.liftToX
#check S2064PasteProblem.liftToY
#check S2064PasteProblem.firstBlock
#check S2064PasteFirstBlockStatement
#check S2064PasteFirstBlockStatement_holds
#check S2064PasteProblem.toS2050
#check S2064PasteProblem.toS2050FirstBlock

#print axioms S2064PasteProblem.lift
#print axioms S2064PasteProblem.liftToX
#print axioms S2064PasteProblem.liftToY
#print axioms S2064PasteProblem.firstBlock
#print axioms S2064PasteFirstBlockStatement_holds

end LeanFormal.IUT.XiFPaper.S2064PasteLiftActual

end
