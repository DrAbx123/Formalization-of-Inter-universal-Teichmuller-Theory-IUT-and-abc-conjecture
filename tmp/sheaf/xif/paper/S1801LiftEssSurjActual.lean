/-
# S1801: S1784LiftEssSurj is not a consequence of the two-pullback witness

## What is decided here

S1784 reduced S1756FirstMissing to the statement

  S1784LiftEssSurj A : for every cone c with apex W and every f : W --> P,
     f >> toX ~ c.toX --> f >> toY ~ c.toY --> Nonempty (f ~ lift c),

for the identity-point base-change square P = S_A.  This file shows that the
*schematic* form of that statement -- the form in which S1784 actually uses it,
i.e. the assertion that the recorded TwoPullbackWitness fields alone force the
conclusion -- is FALSE, and records the exact 2-categorical condition that has
to replace it.

## Results

1. S1801EssSurjOf sq w is the S1784 conclusion stated for an arbitrary
   two-commutative square sq with a recorded two-pullback witness w; this is
   definitionally the body of S1784LiftEssSurj A for the square
   S1743Square A and the witness (S1743BaseChange A).isPullback.

2. REFUTATION.  S1801NoGenericEssSurj: there is no theorem of the form
   'for every square and every TwoPullbackWitness, S1801EssSurjOf holds'.
   The counterexample is the degenerate square of the S1784 header, made
   explicit over the category of test schemes:

   * P is the constant pseudofunctor at the two-point discrete category
     Discrete (Fin 2);
   * the source X, the base Y and the orbicurve Z are the constant
     pseudofunctor at the point category Discrete PUnit;
   * both legs P --> X, P --> Y are the canonical collapse of a functor into
     the point; the lower two legs are identities;
   * the witness takes lift := the constant-at-zero point of P, and its
     comparison 2-cells exist because every two maps into the point are
     2-isomorphic.  twoCell_ext holds because 2-cells into Discrete (Fin 2)
     are unique.

   The square has no invertible 2-cell between the identity of P and the
   constant-at-zero lift (S1801DegenerateNotIso: evaluated at the object 1 of
   Discrete (Fin 2) a 2-cell would give 1 = 0).  Hence the schema fails: the
   model point (identity of P) does not come from the lift, i.e. a model point
   of a non-representable source is not produced by the identity-point square.
   The three projection/comparison 2-cells in this example are canonical
   (associators, unitors, S1801IsoToOne), so the failure is not an artefact of
   a badly chosen 2-cell: it is exactly the missing EXISTENCE of 2-cells, not
   the missing coherence of given ones.

3. THE CORRECT CONDITION.  S1801TwoCellSurjTo and S1801TwoCellSurjFrom record
   the two directions of 2-cell surjectivity of the cone comparison
   Hom(W,P) --> Cone(W) that the recorded witness does not export: for every
   cone c' whose two legs are the two projections of a 1-cell f (the image cone
   of f, supplied with the two equalities), every cone morphism c' --> c
   (respectively c --> c') is realised by a 2-cell f --> lift c (respectively
   lift c --> f) whose projections are exactly that cone morphism composed with
   the comparison isomorphisms of the witness.

   These are the missing EXISTENCE statements for 2-cells.  With them, and with
   the compatibility of the projection isomorphisms (precisely the ConeMorphism
   data used in the definitions), the argument f ~ lift c goes through with no
   fake 2-cell: the two 2-cells are produced by the hypotheses, and the inverse
   law is proved by twoCell_ext, the only 2-cell comparison the recorded witness
   has.  The counterexample above shows that the recorded witness does not imply
   these conditions: if it did, the degenerate square would carry a 2-cell
   id_P ~ const 0, which S1801DegenerateNotIso refutes.

   Consequence for the project: S1784LiftEssSurj A for the identity-point
   square must come from the 2-dimensional universal property of that square
   (fullness of the cone comparison) or from geometry (the monomorphism case of
   S1756, representability of the base), not from the recorded witness alone.

## Axiom footprint

Only propext, Classical.choice and Quot.sound; see the #print axioms block.
No sorry, no new axiom, no Shrink/ULift/PUnit data.
-/

import Iut.Foundations.Orbicurve

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans

/-! ## 0. Setting: the base object -/

variable (F : Type) [Field F]

/-- The base test scheme: Spec F with its identity structure morphism. -/
def S1801BaseObj : LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op (Over.mk (𝟙 (Spec (CommRingCat.of F)))))

/-! ## 1. Constant pseudofunctors into Cat -/

/-- The constant pseudofunctor at a category. -/
def S1801ConstPseudo (C : Type) [Category C] : EtaleStackPseudofunctor F :=
  ((Functor.const (SchemeOverField F)ᵒᵖ).obj (Cat.of C)).toPseudofunctor'

@[simp] lemma S1801ConstPseudo_obj (C : Type) [Category C]
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (S1801ConstPseudo F C).obj U = Cat.of C := rfl

@[simp] lemma S1801ConstPseudo_map (C : Type) [Category C]
    {U V : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (f : U ⟶ V) :
    (S1801ConstPseudo F C).map f = 𝟙 (Cat.of C) := rfl

/-- Two-cells in Cat between functors into the point category are unique. -/
instance S1801SubsingletonHom₂PUnit {C : Cat.{0, 0}}
    (G H : C ⟶ Cat.of (Discrete PUnit.{1})) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Two-cells in Cat between functors into a discrete category are unique. -/
instance S1801SubsingletonHom₂Discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into the point are unique. -/
instance S1801SubsingletonModPUnit {W : EtaleStackPseudofunctor F}
    (a b : Pseudofunctor.StrongTrans W (S1801ConstPseudo F (Discrete PUnit.{1}))) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1801SubsingletonHom₂PUnit (a.app U) (b.app U)).elim _ _

/-- Modifications between strong transformations into a discrete stack are unique. -/
instance S1801SubsingletonModDiscrete {W : EtaleStackPseudofunctor F} {A : Type}
    (a b : Pseudofunctor.StrongTrans W (S1801ConstPseudo F (Discrete A))) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1801SubsingletonHom₂Discrete (a.app U) (b.app U)).elim _ _

/-- The canonical strong transformation into the constant pseudofunctor at the point. -/
def S1801ToOne (W : EtaleStackPseudofunctor F) :
    Pseudofunctor.StrongTrans W (S1801ConstPseudo F (Discrete PUnit.{1})) where
  app U := (Functor.star (W.obj U).α).toCatHom
  naturality {a b} f := by
    apply Cat.Hom.isoMk
    exact Functor.punitExt _ _
  naturality_naturality := by
    intro a b f g eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- Any two strong transformations into the point are 2-isomorphic. -/
noncomputable def S1801IsoToOne {W : EtaleStackPseudofunctor F}
    (a b : Pseudofunctor.StrongTrans W (S1801ConstPseudo F (Discrete PUnit.{1}))) : a ≅ b :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => Cat.Hom.isoMk (Functor.punitExt (a.app U).toFunctor (b.app U).toFunctor))
    (by
      intro x y f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

/-- The constant-at-zero strong transformation into the two-point constant stack. -/
def S1801ConstZero (W : EtaleStackPseudofunctor F) :
    Pseudofunctor.StrongTrans W (S1801ConstPseudo F (Discrete (Fin 2))) where
  app U := ((Functor.const (W.obj U).α).obj (Discrete.mk (0 : Fin 2))).toCatHom
  naturality {a b} f := by
    apply Cat.Hom.isoMk
    exact eqToIso rfl
  naturality_naturality := by
    intro a b f g eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-! ## 2. The S1784 schema -/

/-- The S1784 conclusion for an arbitrary square and witness: essential
surjectivity, in the strong form used by S1784, of the cone comparison. -/
def S1801EssSurjOf {P X Y Z : EtaleStackPseudofunctor F}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor F) (c : sq.Cone W) (f : Pseudofunctor.StrongTrans W P),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY) →
        Nonempty (Iso f (w.lift W c))

/-! ## 3. The degenerate counterexample -/

/-- The point stack. -/
abbrev S1801PointStack : EtaleStackPseudofunctor F :=
  S1801ConstPseudo F (Discrete PUnit.{1})

/-- The two-point stack. -/
abbrev S1801TwoStack : EtaleStackPseudofunctor F :=
  S1801ConstPseudo F (Discrete (Fin 2))

/-- The degenerate two-commutative square: both legs of P collapse to the point. -/
noncomputable def S1801DegenerateSquare :
    EtalePseudofunctorSquare (S1801TwoStack F) (S1801PointStack F)
      (S1801PointStack F) (S1801PointStack F) where
  toX := S1801ToOne F (S1801TwoStack F)
  toY := S1801ToOne F (S1801TwoStack F)
  xToBase := Pseudofunctor.StrongTrans.id (S1801PointStack F)
  yToBase := Pseudofunctor.StrongTrans.id (S1801PointStack F)
  commutes := Iso.refl (Pseudofunctor.StrongTrans.vcomp (S1801ToOne F (S1801TwoStack F))
    (Pseudofunctor.StrongTrans.id (S1801PointStack F)))

/-- The recorded two-pullback witness for the degenerate square. -/
noncomputable def S1801DegenerateWitness :
    (S1801DegenerateSquare F).TwoPullbackWitness where
  lift W c := S1801ConstZero F W
  liftToX W c :=
    S1801IsoToOne F (Pseudofunctor.StrongTrans.vcomp (S1801ConstZero F W)
      (S1801DegenerateSquare F).toX) c.toX
  liftToY W c :=
    S1801IsoToOne F (Pseudofunctor.StrongTrans.vcomp (S1801ConstZero F W)
      (S1801DegenerateSquare F).toY) c.toY
  liftTwoCell W source target m := 𝟙 (S1801ConstZero F W)
  liftTwoCell_toX := by
    intro W source target m
    exact (S1801SubsingletonModPUnit F _ _).elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact (S1801SubsingletonModPUnit F _ _).elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S1801SubsingletonModDiscrete F (W := W) (A := Fin 2) first second).elim alpha beta

/-- The identity cone of the two-point stack. -/
noncomputable def S1801DegenerateCone : (S1801DegenerateSquare F).Cone (S1801TwoStack F) where
  toX := Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1801TwoStack F))
    (S1801DegenerateSquare F).toX
  toY := Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (S1801TwoStack F))
    (S1801DegenerateSquare F).toY
  commutes := S1801IsoToOne F _ _

/-- The identity of the two-point stack is not 2-isomorphic to the constant-at-zero lift:
evaluated at the object 1 of Discrete (Fin 2), a 2-cell would give 1 = 0. -/
theorem S1801DegenerateNotIso :
    ¬ Nonempty (Iso (Pseudofunctor.StrongTrans.id (S1801TwoStack F))
      (S1801ConstZero F (S1801TwoStack F))) := by
  rintro ⟨e⟩
  have h := (e.hom.as.app (S1801BaseObj F)).toNatTrans.app (Discrete.mk (1 : Fin 2))
  have h₂ : (Discrete.mk (1 : Fin 2) : Discrete (Fin 2)) = Discrete.mk 0 := by
    apply Discrete.ext
    show (1 : Fin 2) = 0
    exact Discrete.eq_of_hom h
  exact absurd (congrArg Discrete.as h₂) (by decide)

/-- The S1784 schema fails for the degenerate square and its recorded witness. -/
theorem S1801DegenerateEssSurjFalse :
    ¬ S1801EssSurjOf F (sq := S1801DegenerateSquare F) (S1801DegenerateWitness F) := by
  intro h
  apply S1801DegenerateNotIso F
  exact h (S1801TwoStack F) (S1801DegenerateCone F) (Pseudofunctor.StrongTrans.id (S1801TwoStack F))
    ⟨Iso.refl _⟩ ⟨Iso.refl _⟩

/-- **Refutation of the schematic form**: the two-pullback witness does not, in
general, give the S1784 essential-surjectivity statement. -/
theorem S1801NoGenericEssSurj :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor F) (sq : EtalePseudofunctorSquare P X Y Z)
      (w : sq.TwoPullbackWitness), S1801EssSurjOf F sq w) := by
  intro h
  exact S1801DegenerateEssSurjFalse F (h _ _ _ _ (S1801DegenerateSquare F) (S1801DegenerateWitness F))

/-! ## 4. The correct condition: 2-cell surjectivity of the cone comparison -/

/-- Forward 2-cell surjectivity of the cone comparison, recorded as the correct
additional hypothesis on the square.  For every cone c' whose two legs are the
two projections of a 1-cell f (the image cone of f, supplied with the two
equalities), every cone morphism c' --> c is realised by a 2-cell f --> lift c
whose two projections are exactly that cone morphism composed with the
comparison isomorphisms of the witness.

The recorded TwoPullbackWitness exports only the other direction -- a 2-cell
determines a cone morphism (liftTwoCell, twoCell_ext).  This definition records
the missing existence of 2-cells, i.e. fullness of the comparison
Hom(W,P) --> Cone(W) on compatible pairs; together with the symmetric
S1801TwoCellSurjFrom it gives f ~ lift c for compatible projection
isomorphisms, the inverse law being proved by twoCell_ext (the only 2-cell
comparison the witness provides).  The counterexample above shows that the
recorded witness does not imply these conditions. -/
def S1801TwoCellSurjTo {P X Y Z : EtaleStackPseudofunctor F}
    {sq : EtalePseudofunctorSquare P X Y Z} (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor F) (c c' : sq.Cone W) (f : Pseudofunctor.StrongTrans W P)
    (m : sq.ConeMorphism c' c)
    (hX : c'.toX = Pseudofunctor.StrongTrans.vcomp f sq.toX)
    (hY : c'.toY = Pseudofunctor.StrongTrans.vcomp f sq.toY),
    ∃ u : f ⟶ w.lift W c,
      Pseudofunctor.StrongTrans.whiskerRight u sq.toX =
          eqToHom hX.symm ≫ m.toX ≫ (w.liftToX W c).inv ∧
        Pseudofunctor.StrongTrans.whiskerRight u sq.toY =
          eqToHom hY.symm ≫ m.toY ≫ (w.liftToY W c).inv

/-- Backward 2-cell surjectivity, the symmetric direction: every cone morphism
c --> c' into the image cone of f is realised by a 2-cell lift c --> f. -/
def S1801TwoCellSurjFrom {P X Y Z : EtaleStackPseudofunctor F}
    {sq : EtalePseudofunctorSquare P X Y Z} (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor F) (c c' : sq.Cone W) (f : Pseudofunctor.StrongTrans W P)
    (m : sq.ConeMorphism c c')
    (hX : c'.toX = Pseudofunctor.StrongTrans.vcomp f sq.toX)
    (hY : c'.toY = Pseudofunctor.StrongTrans.vcomp f sq.toY),
    ∃ v : w.lift W c ⟶ f,
      Pseudofunctor.StrongTrans.whiskerRight v sq.toX =
          (w.liftToX W c).hom ≫ m.toX ≫ eqToHom hX ∧
        Pseudofunctor.StrongTrans.whiskerRight v sq.toY =
          (w.liftToY W c).hom ≫ m.toY ≫ eqToHom hY
/-! ## 5. Checks -/

#check @S1801EssSurjOf
#check @S1801NoGenericEssSurj
#check @S1801DegenerateNotIso
#check @S1801TwoCellSurjTo
#check @S1801TwoCellSurjFrom

#print axioms S1801DegenerateNotIso
#print axioms S1801DegenerateEssSurjFalse
#print axioms S1801NoGenericEssSurj
#print axioms S1801TwoCellSurjTo
#print axioms S1801TwoCellSurjFrom

end LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual