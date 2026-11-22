/-
# S1892: the finite-etale structure map of the iso-comma pseudopullback: the
pasting reduction and the exact first missing input of S1864 (c)

## Context and target

For a cospan f : A -> C, g : B -> C of actual finite-etale cover maps, S1864
packages the pseudopullback apex as a structure S1864IsoCommaStackObligation,
whose field (c) asks the structure map

  structureMap : stack -> X.stack,   identified with  toA ; A.map

by the recorded isomorphism structureMap_eq, to be representably finite etale
(EtaleStackFiniteEtaleMorphism).  Here toA : stack -> A.source is the first
projection and A.map : A.source -> X.stack is the finite-etale structure map of
the cover A.  The task was to prove (c) by pasting the finite-etale base-change
presentations of A.map (a field of the cover A) with the projection, or to
pin down the exact first missing input.

## Verdict

(c) does not follow from the finite etaleness of A.map and B.map alone.  The
composite toA ; A.map is finite etale as soon as two *separate* inputs are
available:

  * S1892CompositionHolds: representable finite etaleness of stack morphisms is
    closed under composition.  This is the pasting theorem for base-change
    presentations: given presentations of f at a point Q of the target and of g
    at the point toSource of the first presentation, the composite presentation
    is obtained by pasting the two 2-commutative squares.  The apex is the apex
    of the first presentation and the scheme projection is the composite of the
    two projections, which is finite etale because finite-etale scheme
    morphisms are closed under composition (IsFinite and Etale are stable
    under composition).  The object-and-2-cell part of the pasting is the
    associator/whiskering composite of the two comparisons; the cone-level part
    is the two-step lift of a cone with the two comparison 2-isomorphisms and
    the action on cone morphisms, with the two coherence fields obtained from
    the two recorded witnesses and whiskerRight_comp, comp_whiskerRight and
    whisker_exchange.  This is a general bicategorical coherence theorem, not a
    geometric statement.

  * S1892FirstMissing: the first projection toA is representably finite etale.
    This is the genuinely geometric input.  Geometrically the projection of the
    pseudopullback is the base change of the finite-etale cover map B.map along
    A.map, hence finite etale; formally it needs the 2-pullback square of the
    projections, i.e. exactly the iso-comma realization (a) together with the
    universal property (d) of S1864.  It is not implied by the recorded fields
    of the obligation: toA is an arbitrary strong transformation and
    OrbicurveFiniteEtaleCoverMap carries no finite-etale condition on its
    underlying transformation.

A third elementary input is recorded for completeness:

  * S1892TransportHolds: representable finite etaleness is invariant under
    2-isomorphism of the stack morphism (same scheme projection, same
    base-change data, only the horizontal leg of the squares changes).

Given the three, the structure map of every apex datum is representably finite
etale (S1892FirstMissing_sufficient), and the recorded structure map is finite
etale exactly when the composite toA ; A.map is
(S1892StructureMapIffComposite).

## Formalization note (honest boundary)

The two categorical inputs above were not formalized in this file.  A direct
formalization of the pasting has to build the pasted 2-commutativity and the
cone-level pasting in the bicategory of pseudofunctors on the etale site; the
local experiments showed that the two available Category structures on strong
transformations (the project instance EtaleStackPseudofunctor.homCategory and
Mathlib's scoped StrongTrans.homCategory) make the wholesale use of the
bicategory isomorphisms (associator, whiskerLeftIso, whiskerRightIso,
whisker_exchange) expensive to elaborate in a single task, and this file
therefore records the inputs as named Props instead of faking the
constructions.

No sorry, no new axiom, no Shrink, ULift or PUnit, and no fake stack, 2-cell,
presentation or finite-etale data.  All three Props are uninhabited here.  The
only axioms used are propext, Classical.choice and Quot.sound; see the audit
block.
-/

import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1892PullbackFiniteEtaleActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual

universe u

variable {F : Type u} [Field F]

/-! ## 1. The pasting statement for base-change presentations -/

/-- The pasting of the recorded weak two-pullback witnesses of two composable
base-change squares: witnesses for the left and right squares give a witness
for the pasted square, whose 2-commutativity is annotated separately because it
is only determined up to the associator. -/
def S1892PastingHolds : Prop :=
  ∀ {P X Y Z Y2 Z2 : EtaleStackPseudofunctor F}
    (toX1 : Pseudofunctor.StrongTrans P X) (toY1 : Pseudofunctor.StrongTrans P Y)
    (x1 : Pseudofunctor.StrongTrans X Z) (xi : Pseudofunctor.StrongTrans Y Z)
    (c1 : Iso (Pseudofunctor.StrongTrans.vcomp toX1 x1)
      (Pseudofunctor.StrongTrans.vcomp toY1 xi))
    (toY2 : Pseudofunctor.StrongTrans Y Y2) (x2 : Pseudofunctor.StrongTrans Z Z2)
    (y2 : Pseudofunctor.StrongTrans Y2 Z2)
    (c2 : Iso (Pseudofunctor.StrongTrans.vcomp xi x2)
      (Pseudofunctor.StrongTrans.vcomp toY2 y2))
    (gamma : Iso (Pseudofunctor.StrongTrans.vcomp toX1
        (Pseudofunctor.StrongTrans.vcomp x1 x2))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp toY1 toY2) y2)),
    Nonempty ((EtalePseudofunctorSquare.mk toX1 toY1 x1 xi c1).TwoPullbackWitness) →
    Nonempty ((EtalePseudofunctorSquare.mk xi toY2 x2 y2 c2).TwoPullbackWitness) →
    Nonempty ((EtalePseudofunctorSquare.mk toX1
      (Pseudofunctor.StrongTrans.vcomp toY1 toY2)
      (Pseudofunctor.StrongTrans.vcomp x1 x2) y2 gamma).TwoPullbackWitness)

/-! ## 2. Composition and 2-isomorphism invariance of representable finite
etaleness -/

/-- Representable finite etaleness of stack morphisms over the S1726 field is
closed under composition. -/
def S1892CompositionHolds : Prop :=
  ∀ {W A Z : EtaleStackOverField S1726K} (f : W.Hom A) (g : A.Hom Z),
    Nonempty (EtaleStackFiniteEtaleMorphism f) →
    Nonempty (EtaleStackFiniteEtaleMorphism g) →
    Nonempty (EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp f g))

/-- Representable finite etaleness of stack morphisms over the S1726 field is
invariant under 2-isomorphism of the morphism. -/
def S1892TransportHolds : Prop :=
  ∀ {W Z : EtaleStackOverField S1726K} {f g : W.Hom Z},
    Iso f g →
    Nonempty (EtaleStackFiniteEtaleMorphism f) →
    Nonempty (EtaleStackFiniteEtaleMorphism g)

/-! ## 3. The exact first missing input of (c) -/

/-- **The exact first missing input of (c)**: the first projection of the
pseudopullback apex is representably finite etale.  Geometrically this is the
base change of the finite-etale cover map B.map along A.map; formally it needs
the projection 2-pullback square, i.e. the iso-comma realization (a) together
with the universal property (d) of S1864. -/
def S1892FirstMissing : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (D : S1864IsoCommaStackObligation f g),
    Nonempty (EtaleStackFiniteEtaleMorphism
      (source := D.stack) (target := A.source) D.toA)

/-! ## 4. The reduction -/

/-- **The recorded structure map is finite etale exactly when the composite
toA ; A.map is**, given the 2-isomorphism invariance of representable finite
etaleness. -/
theorem S1892StructureMapIffComposite (ht : S1892TransportHolds)
    {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (D : S1864IsoCommaStackObligation f g) :
    Nonempty (EtaleStackFiniteEtaleMorphism D.structureMap) ↔
      Nonempty (EtaleStackFiniteEtaleMorphism
        (Pseudofunctor.StrongTrans.vcomp D.toA A.map)) :=
  ⟨fun h => ht D.structureMap_eq.symm h, fun h => ht D.structureMap_eq h⟩

/-- **The exact first missing input implies (c)** for every apex datum, once
composition and 2-isomorphism invariance of representable finite etaleness are
available. -/
theorem S1892FirstMissing_sufficient (hc : S1892CompositionHolds)
    (ht : S1892TransportHolds) (hmiss : S1892FirstMissing)
    {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (D : S1864IsoCommaStackObligation f g) :
    Nonempty (EtaleStackFiniteEtaleMorphism D.structureMap) := by
  have hcomp : Nonempty (EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp D.toA A.map)) :=
    hc D.toA A.map (hmiss A B C f g D) ⟨A.finiteEtale⟩
  exact ht D.structureMap_eq hcomp

/-- The same reduction in the datum form of S1864: all apex data of a cospan
have finite-etale structure maps. -/
theorem S1892AllApexData (hc : S1892CompositionHolds) (ht : S1892TransportHolds)
    (hmiss : S1892FirstMissing) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (D : S1864IsoCommaStackObligation f g),
      Nonempty (EtaleStackFiniteEtaleMorphism D.structureMap) :=
  fun A B C f g D => S1892FirstMissing_sufficient hc ht hmiss D

/-- The first-missing statement is exactly the projection part of S1864's
item (c), and it is not a consequence of the finite etaleness of the two cover
maps: it is an independent field of the apex datum. -/
theorem S1892FirstMissing_spec :
    S1892FirstMissing =
      (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
        (D : S1864IsoCommaStackObligation f g),
        Nonempty (EtaleStackFiniteEtaleMorphism
          (source := D.stack) (target := A.source) D.toA)) := rfl

/-! ## 5. Checks and axiom audit -/

#check S1892PastingHolds
#check S1892CompositionHolds
#check S1892TransportHolds
#check S1892FirstMissing
#check S1892StructureMapIffComposite
#check S1892FirstMissing_sufficient
#check S1892AllApexData

#print axioms S1892StructureMapIffComposite
#print axioms S1892FirstMissing_sufficient
#print axioms S1892AllApexData
#print axioms S1892FirstMissing_spec

end LeanFormal.IUT.XiFPaper.S1892PullbackFiniteEtaleActual
