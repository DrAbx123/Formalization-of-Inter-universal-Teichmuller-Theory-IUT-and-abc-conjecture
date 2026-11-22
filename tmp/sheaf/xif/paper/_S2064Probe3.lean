import Iut.Foundations.Orbicurve

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S2064Probe3

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut

universe u
variable {F : Type u} [Field F]

/-- Associator of the pseudofunctor bicategory, in the shape used below. -/
noncomputable def S2064AssociatorIso
    {A B C D : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) :=
  Bicategory.associator (B := EtaleStackPseudofunctor F) f g h

/-- Right whiskering of a 2-isomorphism, in the shape used below. -/
noncomputable def S2064WhiskerRightIso
    {A B C : EtaleStackPseudofunctor F}
    {f f' : Pseudofunctor.StrongTrans A B} (e : Iso f f')
    (g : Pseudofunctor.StrongTrans B C) :
    Iso (Pseudofunctor.StrongTrans.vcomp f g)
      (Pseudofunctor.StrongTrans.vcomp f' g) :=
  Bicategory.whiskerRightIso (B := EtaleStackPseudofunctor F) e g

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

noncomputable abbrev toSquare : EtalePseudofunctorSquare P2 W P1 Y where
  toX := s.toX
  toY := s.toY
  xToBase := sq1.xToBase
  yToBase := Pseudofunctor.StrongTrans.vcomp sq1.toY sq1.yToBase
  commutes := s.commutes

end S2064SecondSquare

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

noncomputable abbrev composite : EtalePseudofunctorSquare p.P2 p.W p.S p.Y where
  toX := p.sq2.toX
  toY := Pseudofunctor.StrongTrans.vcomp p.sq2.toY p.sq1.toY
  xToBase := p.sq1.xToBase
  yToBase := p.sq1.yToBase
  commutes := p.sq2.commutes.trans
    (S2064AssociatorIso p.sq2.toY p.sq1.toY p.sq1.yToBase).symm

noncomputable abbrev cone1 {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : p.sq1.Cone W' where
  toX := cone.toX
  toY := cone.toY
  commutes := cone.commutes

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

noncomputable abbrev lift {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') : Pseudofunctor.StrongTrans W' p.P2 :=
  p.w2.lift W' (p.cone2 cone)

noncomputable abbrev liftToX {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') :
    Iso (Pseudofunctor.StrongTrans.vcomp (p.lift cone) p.composite.toX) cone.toX :=
  p.w2.liftToX W' (p.cone2 cone)

noncomputable abbrev liftToY {W' : EtaleStackPseudofunctor F}
    (cone : p.composite.Cone W') :
    Iso (Pseudofunctor.StrongTrans.vcomp (p.lift cone) p.composite.toY) cone.toY :=
  (S2064AssociatorIso (p.w2.lift W' (p.cone2 cone)) p.sq2.toY p.sq1.toY).symm.trans
    ((S2064WhiskerRightIso (p.w2.liftToY W' (p.cone2 cone)) p.sq1.toY).trans
      (p.w1.liftToY W' (p.cone1 cone)))

end S2064PasteProblem

end LeanFormal.IUT.XiFPaper.S2064Probe3

end
