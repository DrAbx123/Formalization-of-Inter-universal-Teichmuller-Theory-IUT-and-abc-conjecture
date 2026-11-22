import Iut.Foundations.Orbicurve

/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2062
-/

/-!
# S2062: pasting of two 2-pullback squares and composition of base-change presentations

This file implements the two API items of the S2046/S2050 list which are needed
for the D6(c) finite-etale composition closure:

1. Iut.EtalePseudofunctorSquare.TwoPullbackWitness.paste: the pasting of the
   recorded bicategorical pullback data of two vertically composable
   EtalePseudofunctorSquares.
2. Iut.EtaleStackBaseChangePresentation.comp: composition of base-change
   presentations, whose square is the paste of the two presentation squares.
   Additionally Iut.SchemeRepresentableMap.comp supplies the composite
   projection.

## The pasted square

Given a top square (toX, toY, xToBase, commutes) whose horizontal leg toY lands
on the apex of a bottom square bottom : EtalePseudofunctorSquare N M L M', the
pasted square is

  toX = toX,  toY = toY ; bottom.toY,
  xToBase = xToBase ; bottom.xToBase,  yToBase = bottom.yToBase,

with 2-commutativity pasteCommutes the associator/whisker composite of the top
comparison and bottom.commutes.  The consumer only uses the case in which the
shared leg is literally bottom.toX, which is the form used here (this avoids an
unnecessary transport along a 2-isomorphism).

## The cone-level pasting

A cone over the pasted square gives a cone over the bottom square
(pasteConeBottom: first leg cone.toX ; xToBase), and its wbottom-lift then gives
a cone over the top square (pasteConeTop).  Applying the two witnesses in that
order produces the lift.  The comparison isomorphisms liftToX, liftToY and the
action on cone morphisms liftTwoCell are built from the two witnesses plus
pasteAssocIso/pasteWhiskerRightIso/pasteWhiskerLeftIso (whisker wrappers
supplied here because this tree carries two Category structures on strong
transformations, which makes the bare Bicategory projections expensive to
elaborate).

## The three coherence inputs

The three genuine coherence inputs are proved in the auxiliary namespace
Iut.PasteCoherence, as statements about an arbitrary bicategory, and then
instantiated in the pseudofunctor bicategory:

* pasteCompatBottom: compatibility of the induced morphism of bottom cones
  (uses whiskerRight_comp).
* pasteCompatTop: compatibility of the induced morphism of top cones
  (uses wbottom.liftTwoCell_toX).
* pasteCompatToY: the second comparison equation of the pasted witness
  (uses whiskerRight_comp, comp_whiskerRight and liftTwoCell_toY of both
  witnesses).

## The 2-cell faithfulness boundary (honest)

The recorded TwoPullbackWitness.twoCell_ext field of the composite square asks
for joint faithfulness of (top.toX, toY ; bottom.toY).  The two input witnesses
only provide joint faithfulness of (toX, toY) and of (bottom.toX, bottom.toY):
whiskerRight_comp turns the hypothesis into
(a |> bottom.toY) = (b |> bottom.toY), and cancelling the right whiskering by
bottom.toY is not available.  That cancellation is false in general (in the
bicategory of categories take bottom.toY the constant functor to the terminal
category and bottom.toX faithful); so the unconditional paste is not derivable
from the recorded fields.  paste therefore takes the faithful-apex input

  hsub : forall {W f g}, Subsingleton (f ⟶ g)

which is exactly what the composite square's twoCell_ext needs.  For the
consumer in item 2 the apex is a representable pseudofunctor, whose values are
discrete categories, and subsingleton_strongTrans_schemeRepresentable proves
hsub unconditionally.  Hence EtaleStackBaseChangePresentation.comp has no extra
hypotheses, and no witness is weakened or fabricated.

## Exact remaining API

The only missing item for the unconditional paste statement is the cancellation
principle

  forall {a b c} (g : b ⟶ c) {f f' : a ⟶ b} (eta th : f ⟶ f'),
    eta |> g = th |> g -> eta = th

for the middle leg of the pasting (equivalently: the full 2-dimensional
universal property of the recorded square in place of twoCell_ext).  For the
representable apexes of the D6(c) consumer, hsub is proved outright, so no
consumer statement is left conditional.

No sorry, no new axiom, no Prop/Nonempty gate and no fake witness; the axiom
audit is at the end of the file.
-/



noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Iut

namespace PasteCoherence

open CategoryTheory CategoryTheory.Bicategory

universe v u
variable {B : Type u} [Bicategory.{v, u} B]

/-- Coherence for the lower cone morphism of a pasted square. -/
theorem pasteCompatBottom {a b m l m' : B} {Us Ut : a ⟶ b} (nn : Us ⟶ Ut)
    {Vs Vt : a ⟶ l} (mq : Vs ⟶ Vt) (g : b ⟶ m) (bb : m ⟶ m') (y : l ⟶ m')
    (cs : Us ≫ (g ≫ bb) ≅ Vs ≫ y) (ct : Ut ≫ (g ≫ bb) ≅ Vt ≫ y)
    (hcomp : (nn ▷ (g ≫ bb)) ≫ ct.hom = cs.hom ≫ (mq ▷ y)) :
    ((nn ▷ g) ▷ bb) ≫ ((α_ Ut g bb).hom ≫ ct.hom) =
      ((α_ Us g bb).hom ≫ cs.hom) ≫ (mq ▷ y) := by
  have h1 : nn ▷ (g ≫ bb) = (α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom :=
    whiskerRight_comp nn g bb
  have h2 : ((α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom) ≫ ct.hom =
      cs.hom ≫ (mq ▷ y) := by
    rw [← h1]
    exact hcomp
  calc ((nn ▷ g) ▷ bb) ≫ ((α_ Ut g bb).hom ≫ ct.hom)
      = (α_ Us g bb).hom ≫
          (((α_ Us g bb).inv ≫ ((nn ▷ g) ▷ bb) ≫ (α_ Ut g bb).hom) ≫ ct.hom) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (α_ Us g bb).hom ≫ (cs.hom ≫ (mq ▷ y)) := by rw [h2]
    _ = ((α_ Us g bb).hom ≫ cs.hom) ≫ (mq ▷ y) := by rw [Category.assoc]

/-- Coherence for the upper cone morphism of a pasted square. -/
theorem pasteCompatTop {a b n m : B} {Us Ut : a ⟶ b} (nn : Us ⟶ Ut)
    {Vs Vt : a ⟶ n} (wc : Vs ⟶ Vt) (g : b ⟶ m) (y : n ⟶ m)
    (Bs : Vs ≫ y ≅ Us ≫ g) (Bt : Vt ≫ y ≅ Ut ≫ g)
    (hyp : wc ▷ y = Bs.hom ≫ (nn ▷ g) ≫ Bt.inv) :
    (nn ▷ g) ≫ Bt.inv = Bs.inv ≫ (wc ▷ y) := by
  rw [hyp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Coherence for the second projection of a pasted cone. -/
theorem pasteCompatToY {a p n l : B} {Ls Lt : a ⟶ p} (wtc : Ls ⟶ Lt)
    (tY : p ⟶ n) (bY : n ⟶ l)
    {Vs Vt : a ⟶ l} (mq : Vs ⟶ Vt)
    {Dbs Dbt : a ⟶ n} (wbc : Dbs ⟶ Dbt)
    (Cs : Ls ≫ tY ≅ Dbs) (Ct : Lt ≫ tY ≅ Dbt)
    (Ds : Dbs ≫ bY ≅ Vs) (Dt : Dbt ≫ bY ≅ Vt)
    (h1 : wtc ▷ tY = Cs.hom ≫ wbc ≫ Ct.inv)
    (h2 : wbc ▷ bY = Ds.hom ≫ mq ≫ Dt.inv) :
    wtc ▷ (tY ≫ bY) =
      ((α_ Ls tY bY).inv ≫ ((Cs.hom ▷ bY) ≫ Ds.hom)) ≫ mq ≫
        ((Dt.inv ≫ (Ct.inv ▷ bY)) ≫ (α_ Lt tY bY).hom) := by
  have hw : wtc ▷ (tY ≫ bY) = (α_ Ls tY bY).inv ≫ ((wtc ▷ tY) ▷ bY) ≫ (α_ Lt tY bY).hom :=
    whiskerRight_comp wtc tY bY
  rw [hw, h1]
  simp only [comp_whiskerRight]
  rw [h2]
  simp only [Category.assoc]

end PasteCoherence

namespace EtalePseudofunctorSquare

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u
variable {F : Type u} [Field F]

noncomputable def pasteAssocIso {A B' C D : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B') (g : Pseudofunctor.StrongTrans B' C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) :=
  Bicategory.associator (B := EtaleStackPseudofunctor F) f g h

noncomputable def pasteWhiskerRightIso {A B' C : EtaleStackPseudofunctor F}
    {f f' : Pseudofunctor.StrongTrans A B'} (e : Iso f f') (g : Pseudofunctor.StrongTrans B' C) :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f' g) :=
  Bicategory.whiskerRightIso (B := EtaleStackPseudofunctor F) e g

noncomputable def pasteWhiskerLeftIso {A B' C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B') {g g' : Pseudofunctor.StrongTrans B' C} (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f g') :=
  Bicategory.whiskerLeftIso (B := EtaleStackPseudofunctor F) f e

noncomputable def pasteCommutes {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX)) :
    Iso (Pseudofunctor.StrongTrans.vcomp toX
          (Pseudofunctor.StrongTrans.vcomp xToBase bottom.xToBase))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp toY bottom.toY) bottom.yToBase) := by
  have e1 : Iso (Pseudofunctor.StrongTrans.vcomp toX
        (Pseudofunctor.StrongTrans.vcomp xToBase bottom.xToBase))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toX xToBase) bottom.xToBase) :=
    (pasteAssocIso toX xToBase bottom.xToBase).symm
  have e2 : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toX xToBase) bottom.xToBase)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toY bottom.toX) bottom.xToBase) :=
    pasteWhiskerRightIso commutes bottom.xToBase
  have e3 : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toY bottom.toX) bottom.xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY
        (Pseudofunctor.StrongTrans.vcomp bottom.toX bottom.xToBase)) :=
    pasteAssocIso toY bottom.toX bottom.xToBase
  have e4 : Iso (Pseudofunctor.StrongTrans.vcomp toY
        (Pseudofunctor.StrongTrans.vcomp bottom.toX bottom.xToBase))
      (Pseudofunctor.StrongTrans.vcomp toY
        (Pseudofunctor.StrongTrans.vcomp bottom.toY bottom.yToBase)) :=
    pasteWhiskerLeftIso toY bottom.commutes
  have e5 : Iso (Pseudofunctor.StrongTrans.vcomp toY
        (Pseudofunctor.StrongTrans.vcomp bottom.toY bottom.yToBase))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toY bottom.toY) bottom.yToBase) :=
    (pasteAssocIso toY bottom.toY bottom.yToBase).symm
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

/-- The pasted square. -/
noncomputable def pasteSquare {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX)) :
    EtalePseudofunctorSquare P B' L M' where
  toX := toX
  toY := Pseudofunctor.StrongTrans.vcomp toY bottom.toY
  xToBase := Pseudofunctor.StrongTrans.vcomp xToBase bottom.xToBase
  yToBase := bottom.yToBase
  commutes := pasteCommutes toX toY xToBase bottom commutes

/-- The cone over the lower square induced by a cone over the pasted square. -/
noncomputable def pasteConeBottom {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX))
    {W : EtaleStackPseudofunctor F}
    (cone : (pasteSquare toX toY xToBase bottom commutes).Cone W) :
    bottom.Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp cone.toX xToBase
  toY := cone.toY
  commutes := (pasteAssocIso cone.toX xToBase bottom.xToBase).trans cone.commutes

/-- The cone over the upper square induced by a cone over the pasted square. -/
noncomputable def pasteConeTop {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX))
    (wbottom : bottom.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F}
    (cone : (pasteSquare toX toY xToBase bottom commutes).Cone W) :
    (EtalePseudofunctorSquare.mk toX toY xToBase bottom.toX commutes).Cone W where
  toX := cone.toX
  toY := wbottom.lift W (pasteConeBottom toX toY xToBase bottom commutes cone)
  commutes := (wbottom.liftToX W
    (pasteConeBottom toX toY xToBase bottom commutes cone)).symm

/-- A morphism of lower cones induced by a morphism of pasted cones. -/
noncomputable def pasteConeMorphismBottom {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX))
    {W : EtaleStackPseudofunctor F}
    {s t : (pasteSquare toX toY xToBase bottom commutes).Cone W}
    (m : (pasteSquare toX toY xToBase bottom commutes).ConeMorphism s t) :
    bottom.ConeMorphism (pasteConeBottom toX toY xToBase bottom commutes s)
      (pasteConeBottom toX toY xToBase bottom commutes t) where
  toX := Pseudofunctor.StrongTrans.whiskerRight m.toX xToBase
  toY := m.toY
  compatibility := PasteCoherence.pasteCompatBottom (B := EtaleStackPseudofunctor F)
    m.toX m.toY xToBase bottom.xToBase bottom.yToBase s.commutes t.commutes m.compatibility

/-- A morphism of upper cones induced by a morphism of pasted cones. -/
noncomputable def pasteConeMorphismTop {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX))
    (wbottom : bottom.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor F}
    {s t : (pasteSquare toX toY xToBase bottom commutes).Cone W}
    (m : (pasteSquare toX toY xToBase bottom commutes).ConeMorphism s t) :
    (EtalePseudofunctorSquare.mk toX toY xToBase bottom.toX commutes).ConeMorphism
      (pasteConeTop toX toY xToBase bottom commutes wbottom s)
      (pasteConeTop toX toY xToBase bottom commutes wbottom t) where
  toX := m.toX
  toY := wbottom.liftTwoCell W
    (pasteConeBottom toX toY xToBase bottom commutes s)
    (pasteConeBottom toX toY xToBase bottom commutes t)
    (pasteConeMorphismBottom toX toY xToBase bottom commutes m)
  compatibility := PasteCoherence.pasteCompatTop (B := EtaleStackPseudofunctor F)
    m.toX
    (wbottom.liftTwoCell W
      (pasteConeBottom toX toY xToBase bottom commutes s)
      (pasteConeBottom toX toY xToBase bottom commutes t)
      (pasteConeMorphismBottom toX toY xToBase bottom commutes m))
    xToBase bottom.toX
    (wbottom.liftToX W (pasteConeBottom toX toY xToBase bottom commutes s))
    (wbottom.liftToX W (pasteConeBottom toX toY xToBase bottom commutes t))
    (wbottom.liftTwoCell_toX W
      (pasteConeBottom toX toY xToBase bottom commutes s)
      (pasteConeBottom toX toY xToBase bottom commutes t)
      (pasteConeMorphismBottom toX toY xToBase bottom commutes m))

namespace TwoPullbackWitness

/-- Pasting of two two-pullback witnesses, with the 2-cell faithfulness input
on the apex that the composite square twoCell_ext requires. -/
noncomputable def paste {P B' N M L M' : EtaleStackPseudofunctor F}
    (toX : Pseudofunctor.StrongTrans P B') (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX))
    (wtop : (EtalePseudofunctorSquare.mk toX toY xToBase bottom.toX commutes).TwoPullbackWitness)
    (wbottom : bottom.TwoPullbackWitness)
    (hsub : forall {W : EtaleStackPseudofunctor F}
      {f g : Pseudofunctor.StrongTrans W P}, Subsingleton (f ⟶ g)) :
    (pasteSquare toX toY xToBase bottom commutes).TwoPullbackWitness where
  lift W cone := wtop.lift W (pasteConeTop toX toY xToBase bottom commutes wbottom cone)
  liftToX W cone := wtop.liftToX W (pasteConeTop toX toY xToBase bottom commutes wbottom cone)
  liftToY W cone :=
    (pasteAssocIso (wtop.lift W (pasteConeTop toX toY xToBase bottom commutes wbottom cone))
        toY bottom.toY).symm.trans
      ((pasteWhiskerRightIso
          (wtop.liftToY W (pasteConeTop toX toY xToBase bottom commutes wbottom cone))
          bottom.toY).trans
        (wbottom.liftToY W (pasteConeBottom toX toY xToBase bottom commutes cone)))
  liftTwoCell W s t m :=
    wtop.liftTwoCell W (pasteConeTop toX toY xToBase bottom commutes wbottom s)
      (pasteConeTop toX toY xToBase bottom commutes wbottom t)
      (pasteConeMorphismTop toX toY xToBase bottom commutes wbottom m)
  liftTwoCell_toX W s t m :=
    wtop.liftTwoCell_toX W (pasteConeTop toX toY xToBase bottom commutes wbottom s)
      (pasteConeTop toX toY xToBase bottom commutes wbottom t)
      (pasteConeMorphismTop toX toY xToBase bottom commutes wbottom m)
  liftTwoCell_toY W s t m :=
    PasteCoherence.pasteCompatToY (B := EtaleStackPseudofunctor F)
      (wtop.liftTwoCell W (pasteConeTop toX toY xToBase bottom commutes wbottom s)
        (pasteConeTop toX toY xToBase bottom commutes wbottom t)
        (pasteConeMorphismTop toX toY xToBase bottom commutes wbottom m))
      toY bottom.toY
      m.toY
      (wbottom.liftTwoCell W
        (pasteConeBottom toX toY xToBase bottom commutes s)
        (pasteConeBottom toX toY xToBase bottom commutes t)
        (pasteConeMorphismBottom toX toY xToBase bottom commutes m))
      (wtop.liftToY W (pasteConeTop toX toY xToBase bottom commutes wbottom s))
      (wtop.liftToY W (pasteConeTop toX toY xToBase bottom commutes wbottom t))
      (wbottom.liftToY W (pasteConeBottom toX toY xToBase bottom commutes s))
      (wbottom.liftToY W (pasteConeBottom toX toY xToBase bottom commutes t))
      (wtop.liftTwoCell_toY W (pasteConeTop toX toY xToBase bottom commutes wbottom s)
        (pasteConeTop toX toY xToBase bottom commutes wbottom t)
        (pasteConeMorphismTop toX toY xToBase bottom commutes wbottom m))
      (wbottom.liftTwoCell_toY W
        (pasteConeBottom toX toY xToBase bottom commutes s)
        (pasteConeBottom toX toY xToBase bottom commutes t)
        (pasteConeMorphismBottom toX toY xToBase bottom commutes m))
  twoCell_ext W first second alpha beta h1 h2 :=
    (hsub (W := W) (f := first) (g := second)).elim alpha beta

end TwoPullbackWitness

end EtalePseudofunctorSquare

end Iut

namespace Iut

namespace EtalePseudofunctorSquare

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u
variable {F : Type u} [Field F]

/-- 2-cells in Cat valued in a discrete category form a subsingleton. -/
theorem subsingleton_catHom₂ {C : Cat.{u, u}} {X : Type u}
    {f g : C ⟶ Cat.of (Discrete X)} : Subsingleton (f ⟶ g) := by
  refine ⟨fun a b => ?_⟩
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _

/-- Every 2-cell into a representable etale pseudofunctor is trivial: its
objectwise values land in discrete categories. -/
theorem subsingleton_strongTrans_schemeRepresentable {W : EtaleStackPseudofunctor F}
    {S : SchemeOverField F}
    {f g : Pseudofunctor.StrongTrans W (schemeRepresentableEtalePseudofunctor F S)} :
    Subsingleton (f ⟶ g) := by
  refine ⟨fun a b => ?_⟩
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  haveI : Subsingleton (f.app U ⟶ g.app U) := subsingleton_catHom₂
  exact Subsingleton.elim _ _

end EtalePseudofunctorSquare

namespace SchemeRepresentableMap

open CategoryTheory
open scoped Pseudofunctor.StrongTrans

universe u
variable {F : Type u} [Field F]

/-- Composition of scheme-representable maps. -/
noncomputable def comp {source target middle : SchemeOverField F}
    {f : source ⟶ target} {g : target ⟶ middle}
    (F₁ : SchemeRepresentableMap f) (G₁ : SchemeRepresentableMap g) :
    SchemeRepresentableMap (f ≫ g) where
  transformation := Pseudofunctor.StrongTrans.vcomp F₁.transformation G₁.transformation
  app_eq U := by
    apply Cat.ext
    change (F₁.transformation.app (LocallyDiscrete.mk U)).toFunctor ⋙
      (G₁.transformation.app (LocallyDiscrete.mk U)).toFunctor
      = (Discrete.functor (fun P : Opposite.unop U ⟶ source =>
          Discrete.mk (P ≫ (f ≫ g))))
    rw [F₁.app_eq U, G₁.app_eq U]
    simp only [Functor.toCatHom_toFunctor]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      obtain ⟨i⟩ := X
      simp only [Functor.comp_obj, Discrete.functor_obj]
      apply Discrete.ext
      exact Category.assoc _ _ _
    · intro X Y f
      exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _

end SchemeRepresentableMap

namespace EtaleStackBaseChangePresentation

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u
variable {F : Type u} [Field F]

/-- Composition of base-change presentations. -/
noncomputable def comp {A B C : EtaleStackOverField F} {f : A.Hom B} {g : B.Hom C}
    {T : SchemeOverField F}
    {q : Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F T) C.fiber}
    (Pg : EtaleStackBaseChangePresentation g T q)
    (Pf : EtaleStackBaseChangePresentation f Pg.pullbackScheme Pg.toSource) :
    EtaleStackBaseChangePresentation (Pseudofunctor.StrongTrans.vcomp f g) T q := by
  let bottom : EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor F Pg.pullbackScheme) B.fiber
      (schemeRepresentableEtalePseudofunctor F T) C.fiber :=
    EtalePseudofunctorSquare.mk Pg.toSource Pg.projectionMap.transformation g q Pg.commutes
  have hsq : EtalePseudofunctorSquare.pasteSquare Pf.toSource Pf.projectionMap.transformation
      f bottom Pf.commutes
      = EtalePseudofunctorSquare.mk Pf.toSource
          (Pseudofunctor.StrongTrans.vcomp Pf.projectionMap.transformation
            Pg.projectionMap.transformation)
          (Pseudofunctor.StrongTrans.vcomp f g) q
          (EtalePseudofunctorSquare.pasteCommutes Pf.toSource
            Pf.projectionMap.transformation f bottom Pf.commutes) := rfl
  refine
    { pullbackScheme := Pf.pullbackScheme
      projection := Pf.projection ≫ Pg.projection
      projectionMap := SchemeRepresentableMap.comp Pf.projectionMap Pg.projectionMap
      toSource := Pf.toSource
      commutes := EtalePseudofunctorSquare.pasteCommutes Pf.toSource
        Pf.projectionMap.transformation f bottom Pf.commutes
      isPullback := ?_ }
  exact hsq ▸ EtalePseudofunctorSquare.TwoPullbackWitness.paste Pf.toSource
    Pf.projectionMap.transformation f bottom Pf.commutes Pf.isPullback Pg.isPullback
    (fun {_ _} => EtalePseudofunctorSquare.subsingleton_strongTrans_schemeRepresentable)

end EtaleStackBaseChangePresentation

end Iut
namespace LeanFormal.IUT.XiFPaper.S2062TwoPullbackPasteActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut

universe u

#check Iut.EtalePseudofunctorSquare.pasteCommutes
#check Iut.EtalePseudofunctorSquare.pasteSquare
#check Iut.EtalePseudofunctorSquare.pasteConeBottom
#check Iut.EtalePseudofunctorSquare.pasteConeTop
#check Iut.EtalePseudofunctorSquare.TwoPullbackWitness.paste
#check Iut.EtalePseudofunctorSquare.subsingleton_strongTrans_schemeRepresentable
#check Iut.SchemeRepresentableMap.comp
#check Iut.EtaleStackBaseChangePresentation.comp

#print axioms Iut.PasteCoherence.pasteCompatBottom
#print axioms Iut.PasteCoherence.pasteCompatTop
#print axioms Iut.PasteCoherence.pasteCompatToY
#print axioms Iut.EtalePseudofunctorSquare.pasteCommutes
#print axioms Iut.EtalePseudofunctorSquare.pasteSquare
#print axioms Iut.EtalePseudofunctorSquare.pasteConeBottom
#print axioms Iut.EtalePseudofunctorSquare.pasteConeTop
#print axioms Iut.EtalePseudofunctorSquare.pasteConeMorphismBottom
#print axioms Iut.EtalePseudofunctorSquare.pasteConeMorphismTop
#print axioms Iut.EtalePseudofunctorSquare.TwoPullbackWitness.paste
#print axioms Iut.EtalePseudofunctorSquare.subsingleton_catHom₂
#print axioms Iut.EtalePseudofunctorSquare.subsingleton_strongTrans_schemeRepresentable
#print axioms Iut.SchemeRepresentableMap.comp
#print axioms Iut.EtaleStackBaseChangePresentation.comp

end LeanFormal.IUT.XiFPaper.S2062TwoPullbackPasteActual
