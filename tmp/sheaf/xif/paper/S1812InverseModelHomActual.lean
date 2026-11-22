/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1766CanonicalModelInjectivityActual

/-!
# S1812: the inverse of the S1755 model-morphism extraction

## Question

S1755 extracted, from every actual cover map f : S1728CoverMap A B, a model
morphism

  S1755ModelHomOfCoverMap A B f : S1733Model A ⟶ S1733Model B,

by lifting the cone of f through the identity-point two-pullback and applying
S1742's reverse 2-Yoneda comparison.  It proved that this extraction is
faithful on 2-isomorphism classes but did not construct any inverse: that is
S1755ModelHomEquivMissing.

This file constructs the inverse in the only form in which it exists, proves
the round trip F (G g) = g, and determines exactly which additional datum is
missing for the raw two-sided inverse.

## 1. The inverse construction (unconditional)

Two things are needed to turn a model morphism into a cover map: the 1-cell
X ⟶ Y between the cover sources, and the commutes 2-cell.

* The 1-cell is G g := (S1755ModelSectionLift A ≫ S1742StrongTransOfHom g)
  ≫ toSource_B (def. S1812ModelHomToCoverMap).
* The commutes 2-cell is built from

    B.commutes : toSource_B ≫ B.map ≅ projection_B ≫ basePoint,

  the right unitor at the projection (S1733BasePoint is S1733's identity
  1-cell of the representable base stack), the projection comparison
  S1812StrongTransProj : (S1742StrongTransOfHom g) ≫ projection_B ≅
  projection_A, and the unconditional projection half of the model section
  S1755ModelSectionProj : S1755ModelSectionLift A ≫ projection_A ≅ A.map.

The projection comparison is where the slice condition enters.  It is produced
by 2-Yoneda (S1755IsoOfEvalEq) from the equation

  g ≫ S1733ModelOver B = S1733ModelOver A,

because the 2-Yoneda evaluation of the projection is the projection
(S1755ProjectionMap_eval) and that of S1742StrongTransOfHom g is g
(S1742HomOfStrongTrans_strongTransOfHom).

**This triangle is not a consequence of g : S1733Model A ⟶ S1733Model B.**
The models are objects of Over (Spec F'); the triangle in that category only
gives g.left ≫ (model B).hom = (model A).hom, i.e. the same equation after
post-composition with the structure morphism Spec R' ⟶ Spec F', and that
morphism is not a monomorphism.  The natural hom type for the affine models is
therefore the *slice over Spec R'*:

  S1812ModelHomOver A B :=
    { g : S1733Model A ⟶ S1733Model B // g ≫ S1733ModelOver B = S1733ModelOver A }.

This is made formal below: S1812triangle_postcomp proves that the Over triangle
gives the slice triangle only after post-composition with Spec R' ⟶ Spec F',
and S1812overTriangle_of_slice proves that the slice triangle implies the Over
triangle.  So the slice condition is exactly the relative form of the Over
triangle, and the missing step in the unconditional direction is the
cancellation of Spec R' ⟶ Spec F', which is not a monomorphism.

Every value of the extraction lies in this slice, unconditionally
(S1812ModelHomOfCoverMap_triangle).  So the corrected form of the inverse
statement is on S1812ModelHomOver, and S1755ModelHomEquivMissing on all of
S1733Model A ⟶ S1733Model B is stronger than the geometric statement: it
forces every model morphism to be a morphism over Spec R'
(S1812ModelHomEquivMissing_implies_triangle).

## 2. The round trip F (G g) = g (under S1755SourceRetraction)

The missing unit of the two-pullback is used at exactly one place, twice: to
replace a_A ≫ sec_A and a_B ≫ sec_B by the identity, so that the universal lift
of the cone of G g becomes 2-isomorphic to S1742StrongTransOfHom g
(S1812LiftIsoStrongTransOfHom).  2-Yoneda then gives the equation
(S1812ModelHomOfCoverMap_toCoverMap).

## 3. The kernel of the extraction is 2-isomorphism (unconditional)

Two new ingredients make the *other* direction of the kernel theorem provable,
with no hypothesis at all:

* the orbicurve stack of S1726 is *representable* -- it is the representable
  stack of Spec R' by rfl (S1726Orbicurve_stack_fiber); hence 2-cells with
  representable target are subsingletons (S1766_modification_subsingleton);
* the two-pullback witness acts on cone morphisms
  (EtalePseudofunctorSquare.TwoPullbackWitness.liftTwoCell).

From a 2-isomorphism f.map ≅ g.map we get a cone morphism between the cones of
f and g (its compatibility equation is automatic because its two sides are
2-cells into the representable orbicurve stack), hence a 2-cell between the two
lifts, in both directions, hence an isomorphism of lifts.  Therefore

  S1812ModelHomOfCoverMap_eq_iff_coverMapRel :
    F f = F g ↔ S1728CoverMapRel f g

for the S1755 extraction, matching S1766's kernel theorem for the S1744 action.

With that, the extraction descends to the 2-isomorphism quotient, and under
S1755SourceRetraction it is a bijection onto the slice of model morphisms over
the base (S1812QuotSliceEquiv).

## 4. Raw injectivity: the exact residual

The strict two-sided inverse of S1755CoverModelHomEquivData needs the raw cover
maps, not the 2-isomorphism classes.  The remaining gap is exactly

  S1812RawInjective A B : Function.Injective (S1755ModelHomOfCoverMap A B),

which is *equivalent* to S1766's discreteness of cover-map hom types
(S1812RawInjective_iff_discrete): every 2-isomorphism class of cover maps has
a single representative.  It is not a statement about geometry: any
functorially defined action is constant on 2-isomorphism classes (S1766), and
no pair of distinct 2-isomorphic cover maps is available in the tree, so the
statement is neither proved nor refuted here.  This is the "choice of a
representative in each 2-isomorphism class".

The main exact statement of this file is therefore

  S1812ModelHomEquivMissing_iff (h : S1755SourceRetraction) :
    S1755ModelHomEquivMissing ↔
      ((∀ A B g, g ≫ S1733ModelOver B = S1733ModelOver A) ∧
        ∀ A B, S1812RawInjective A B).

## Honest boundary

No sorry, no axiom, no Shrink, no ULift, no PUnit.  The inverse is constructed
on the slice S1812ModelHomOver, not on all Over (Spec F') morphisms; the round
trip needs S1755SourceRetraction; the raw two-sided inverse additionally needs
S1812RawInjective.  None of these is claimed to be proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual

/-! ## 0. Evaluation lemmas in the exact form used below -/

/-- The 2-Yoneda evaluation of a representable projection is the projection. -/
theorem S1812EvalProjectionMap (A : S1728Cover) :
    S1755Eval (S1755BaseChange A).pullbackScheme S1726AffineOver
        (S1755BaseChange A).projectionMap.transformation = S1733ModelOver A :=
  S1755ProjectionMap_eval A

/-- The 2-Yoneda evaluation of the strong transformation of a scheme morphism
is that morphism. -/
theorem S1812EvalStrongTransOfHom {S T : SchemeOverField S1726K} (g : S ⟶ T) :
    S1755Eval S T (S1742StrongTransOfHom (F := S1726K) g) = g :=
  S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) g

/-! ## 1. The slice of model morphisms over the affine base -/

/-- A model morphism *over the affine base*: an Over (Spec F') morphism whose
triangle against the chosen projections to Spec R' commutes.  This is the
natural hom type of the affine models, and the type on which the extraction has
an inverse. -/
def S1812ModelHomOver (A B : S1728Cover) : Type :=
  { g : S1733Model A ⟶ S1733Model B // g ≫ S1733ModelOver B = S1733ModelOver A }

/-- **The triangle that Over (Spec F') actually supplies.**  For a model morphism
the Over triangle is the slice triangle only after post-composition with the
structure morphism Spec R' ⟶ Spec F'.  This is the precise sense in which the
slice condition is an extra datum and not a consequence of the Over triangle. -/
theorem S1812triangle_postcomp (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B) :
    (g.left ≫ (S1733ModelOver B).left) ≫ S1726AffineOver.hom =
      (S1733ModelOver A).left ≫ S1726AffineOver.hom := by
  rw [Category.assoc, Over.w (S1733ModelOver B), Over.w g,
    ← Over.w (S1733ModelOver A)]

/-- Conversely, the slice triangle implies the Over (Spec F') triangle: the slice
condition is exactly the relative form of the Over triangle. -/
theorem S1812overTriangle_of_slice (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B)
    (hg : g.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left) :
    g.left ≫ (S1733Model B).hom = (S1733Model A).hom := by
  rw [← Over.w (S1733ModelOver B), ← Category.assoc, hg,
    Over.w (S1733ModelOver A)]

/-- **Every value of the extraction is a model morphism over the base.**  This is
unconditional and uses only the projection half of the model section. -/
theorem S1812ModelHomOfCoverMap_triangle (A B : S1728Cover)
    (f : S1728CoverMap A B) :
    S1755ModelHomOfCoverMap A B f ≫ S1733ModelOver B = S1733ModelOver A := by
  have h := S1742HomOfStrongTrans_congr (F := S1726K) (S1755Lift_toY A B f)
  have h2 : S1755Eval (S1755BaseChange A).pullbackScheme S1726AffineOver
        ((S1755Lift A B f).vcomp
          (S1755BaseChange B).projectionMap.transformation) =
      S1755Eval (S1755BaseChange A).pullbackScheme S1726AffineOver
        (S1755BaseChange A).projectionMap.transformation := h
  rw [S1755Eval_vcomp] at h2
  rw [show S1755Eval (S1755BaseChange B).pullbackScheme S1726AffineOver
        (S1755BaseChange B).projectionMap.transformation = S1733ModelOver B from
      S1812EvalProjectionMap B] at h2
  rw [show S1755Eval (S1755BaseChange A).pullbackScheme S1726AffineOver
        (S1755BaseChange A).projectionMap.transformation = S1733ModelOver A from
      S1812EvalProjectionMap A] at h2
  exact h2

/-- The extraction as a map into the slice over the affine base. -/
noncomputable def S1812ModelHomOfCoverMapSlice (A B : S1728Cover)
    (f : S1728CoverMap A B) : S1812ModelHomOver A B :=
  ⟨S1755ModelHomOfCoverMap A B f, S1812ModelHomOfCoverMap_triangle A B f⟩

/-! ## 2. The projection comparison -/

/-- **The projection comparison attached to a model morphism over the base.**
The strong transformation induced by g agrees with the model section on the
projection to Spec R'.  This is 2-Yoneda applied to the slice triangle. -/
noncomputable def S1812StrongTransProj (A B : S1728Cover)
    (g : S1733Model A ⟶ S1733Model B)
    (hg : g ≫ S1733ModelOver B = S1733ModelOver A) :
    Iso ((S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
          (T := S1733Model B) g).vcomp
        (S1755BaseChange B).projectionMap.transformation)
      (S1755BaseChange A).projectionMap.transformation := by
  refine S1755IsoOfEvalEq (S := S1733Model A) (T := S1726AffineOver) _ _ ?_
  show S1755Eval (S1733Model A) S1726AffineOver
      ((S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
        (T := S1733Model B) g).vcomp
          (S1755BaseChange B).projectionMap.transformation) =
    S1755Eval (S1733Model A) S1726AffineOver
      (S1755BaseChange A).projectionMap.transformation
  rw [S1755Eval_vcomp]
  rw [show S1755Eval (S1733Model A) (S1733Model B)
        (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
          (T := S1733Model B) g) = g from
      S1812EvalStrongTransOfHom g]
  rw [show S1755Eval (S1733Model B) S1726AffineOver
        (S1755BaseChange B).projectionMap.transformation = S1733ModelOver B from
      S1812EvalProjectionMap B]
  rw [show S1755Eval (S1733Model A) S1726AffineOver
        (S1755BaseChange A).projectionMap.transformation = S1733ModelOver A from
      S1812EvalProjectionMap A]
  exact hg

/-! ## 3. The inverse construction -/

/-- **The inverse of the S1755 extraction on model morphisms over the base.**
G g has underlying 1-cell
(S1755ModelSectionLift A ≫ S1742StrongTransOfHom g) ≫ toSource_B, and its
commutes 2-cell is built from B.commutes, the projection comparison and the
unconditional projection half of the model section. -/
noncomputable def S1812ModelHomToCoverMap (A B : S1728Cover)
    (g : S1812ModelHomOver A B) : S1728CoverMap A B where
  map := ((S1755ModelSectionLift A).vcomp
      (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
        (T := S1733Model B) g.1)).vcomp (S1755BaseChange B).toSource
  commutes := by
    let sec : S1755Source A ⟶ S1755ModelStack A := S1755ModelSectionLift A
    let STg : S1755ModelStack A ⟶ S1755ModelStack B :=
      S1742StrongTransOfHom (F := S1726K) (S := S1733Model A) (T := S1733Model B) g.1
    let aB : S1755ModelStack B ⟶ S1755Source B := (S1755BaseChange B).toSource
    let dB : S1755ModelStack B ⟶ S1755Y S1726AffineOver :=
      (S1755BaseChange B).projectionMap.transformation
    let dA : S1755ModelStack A ⟶ S1755Y S1726AffineOver :=
      (S1755BaseChange A).projectionMap.transformation
    have hG : Iso (STg.vcomp dB) dA := S1812StrongTransProj A B g.1 g.2
    have hB : Iso (aB.vcomp B.map) (dB.vcomp S1733BasePoint) :=
      (S1755BaseChange B).commutes
    have hB' : Iso (aB.vcomp B.map) dB :=
      hB.trans (S1756RightUnitorIso dB)
    have hAssoc : Iso (((sec.vcomp STg).vcomp aB).vcomp B.map)
        ((sec.vcomp STg).vcomp (aB.vcomp B.map)) :=
      S1756AssociatorIso (sec.vcomp STg) aB B.map
    have hWhisk : Iso ((sec.vcomp STg).vcomp (aB.vcomp B.map))
        ((sec.vcomp STg).vcomp dB) :=
      S1756WhiskerLeftIso (sec.vcomp STg) (aB.vcomp B.map) dB hB'
    have hMid : Iso ((sec.vcomp STg).vcomp dB) (sec.vcomp dA) :=
      (S1756AssociatorIso sec STg dB).trans
        (S1756WhiskerLeftIso sec (STg.vcomp dB) dA hG)
    exact hAssoc.trans (hWhisk.trans (hMid.trans (S1755ModelSectionProj A)))

/-- Computation rule for the underlying 1-cell of the inverse construction. -/
theorem S1812ModelHomToCoverMap_map (A B : S1728Cover) (g : S1812ModelHomOver A B) :
    (S1812ModelHomToCoverMap A B g).map =
      ((S1755ModelSectionLift A).vcomp
        (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
          (T := S1733Model B) g.1)).vcomp (S1755BaseChange B).toSource := rfl

/-! ## 4. The round trip F (G g) = g -/

/-- **The lift of the cone of G g is 2-isomorphic to the strong transformation
of g.**  The only missing input used is the unit half of the two-pullback
universal property, toSource ≫ S1755ModelSectionLift ≅ 1. -/
noncomputable def S1812LiftIsoStrongTransOfHom (h : S1755SourceRetraction)
    (A B : S1728Cover) (g : S1812ModelHomOver A B) :
    Iso (S1755Lift A B (S1812ModelHomToCoverMap A B g))
      (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
        (T := S1733Model B) g.1) := by
  let secA : S1755Source A ⟶ S1755ModelStack A := S1755ModelSectionLift A
  let secB : S1755Source B ⟶ S1755ModelStack B := S1755ModelSectionLift B
  let STg : S1755ModelStack A ⟶ S1755ModelStack B :=
    S1742StrongTransOfHom (F := S1726K) (S := S1733Model A) (T := S1733Model B) g.1
  let aA : S1755ModelStack A ⟶ S1755Source A := (S1755BaseChange A).toSource
  let aB : S1755ModelStack B ⟶ S1755Source B := (S1755BaseChange B).toSource
  let mapG : S1755Source A ⟶ S1755Source B := (secA.vcomp STg).vcomp aB
  let L : S1755ModelStack A ⟶ S1755ModelStack B :=
    S1755Lift A B (S1812ModelHomToCoverMap A B g)
  have hSA : Iso (aA.vcomp secA) (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) :=
    (S1755ModelSection_retraction h A).some
  have hSB : Iso (aB.vcomp secB) (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) :=
    (S1755ModelSection_retraction h B).some
  have hL : Iso (L.vcomp aB) (aA.vcomp mapG) := S1755Lift_toX A B _
  have hMS : Iso (mapG.vcomp secB) (secA.vcomp STg) :=
    (S1756AssociatorIso (secA.vcomp STg) aB secB).trans
      ((S1756WhiskerLeftIso (secA.vcomp STg) (aB.vcomp secB)
        (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) hSB).trans
        (S1756RightUnitorIso (secA.vcomp STg)))
  have e1 : Iso L (L.vcomp (aB.vcomp secB)) :=
    (S1756RightUnitorIso L).symm.trans
      ((S1756WhiskerLeftIso L (aB.vcomp secB)
        (Pseudofunctor.StrongTrans.id (S1755ModelStack B)) hSB).symm)
  have e2 : Iso (L.vcomp (aB.vcomp secB)) ((L.vcomp aB).vcomp secB) :=
    (S1756AssociatorIso L aB secB).symm
  have e3 : Iso ((L.vcomp aB).vcomp secB) ((aA.vcomp mapG).vcomp secB) :=
    S1756WhiskerRightIso (L.vcomp aB) (aA.vcomp mapG) secB hL
  have e4 : Iso ((aA.vcomp mapG).vcomp secB) (aA.vcomp (mapG.vcomp secB)) :=
    S1756AssociatorIso aA mapG secB
  have e5 : Iso (aA.vcomp (mapG.vcomp secB)) (aA.vcomp (secA.vcomp STg)) :=
    S1756WhiskerLeftIso aA (mapG.vcomp secB) (secA.vcomp STg) hMS
  have e6 : Iso (aA.vcomp (secA.vcomp STg)) ((aA.vcomp secA).vcomp STg) :=
    (S1756AssociatorIso aA secA STg).symm
  have e7 : Iso ((aA.vcomp secA).vcomp STg)
      ((Pseudofunctor.StrongTrans.id (S1755ModelStack A)).vcomp STg) :=
    S1756WhiskerRightIso (aA.vcomp secA)
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A)) STg hSA
  have e8 : Iso ((Pseudofunctor.StrongTrans.id (S1755ModelStack A)).vcomp STg) STg :=
    S1756LeftUnitorIso STg
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans e8))))))

/-- **The extraction is a right inverse of the constructed map**, under the
missing unit half of the two-pullback universal property. -/
theorem S1812ModelHomOfCoverMap_toCoverMap (h : S1755SourceRetraction)
    (A B : S1728Cover) (g : S1812ModelHomOver A B) :
    S1755ModelHomOfCoverMap A B (S1812ModelHomToCoverMap A B g) = g.1 := by
  have h1 : S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A) (T := S1733Model B)
      (S1755Lift A B (S1812ModelHomToCoverMap A B g)) =
      S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A) (T := S1733Model B)
        (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
          (T := S1733Model B) g.1) :=
    S1742HomOfStrongTrans_congr (F := S1726K) (S1812LiftIsoStrongTransOfHom h A B g)
  have h2 : S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A) (T := S1733Model B)
      (S1742StrongTransOfHom (F := S1726K) (S := S1733Model A)
        (T := S1733Model B) g.1) = g.1 :=
    S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) g.1
  exact h1.trans h2

/-! ## 5. The kernel of the extraction is 2-isomorphism -/

/-- A cone morphism between the cones of two 2-isomorphic cover maps.  The
compatibility equation is automatic, because its two sides are 2-cells into the
representable orbicurve stack (S1766_modification_subsingleton). -/
noncomputable def S1812ConeMorphism {A B : S1728Cover} {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    EtalePseudofunctorSquare.ConeMorphism (S1755Square B)
      (S1755Cone A B f) (S1755Cone A B g) where
  toX := (S1756WhiskerLeftIso (S1755BaseChange A).toSource f.map g.map e).hom
  toY := 𝟙 _
  compatibility := by
    haveI : Subsingleton
        ((S1755Cone A B f).toX.vcomp (S1755Square B).xToBase ⟶
          (S1755Cone A B g).toY.vcomp (S1755Square B).yToBase) :=
      S1766_modification_subsingleton _ _
    exact Subsingleton.elim _ _

/-- **The 2-cell action of the two-pullback on lifts.**  Two 2-isomorphic cover
maps have 2-isomorphic universal lifts. -/
theorem S1812LiftIsoOfMapIso {A B : S1728Cover} {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    Nonempty (Iso (S1755Lift A B f) (S1755Lift A B g)) := by
  let α : S1755Lift A B f ⟶ S1755Lift A B g :=
    (S1755BaseChange B).isPullback.liftTwoCell (S1755ModelStack A)
      (S1755Cone A B f) (S1755Cone A B g) (S1812ConeMorphism e)
  let β : S1755Lift A B g ⟶ S1755Lift A B f :=
    (S1755BaseChange B).isPullback.liftTwoCell (S1755ModelStack A)
      (S1755Cone A B g) (S1755Cone A B f) (S1812ConeMorphism e.symm)
  haveI : Subsingleton (S1755Lift A B f ⟶ S1755Lift A B f) :=
    S1766_modification_subsingleton _ _
  haveI : Subsingleton (S1755Lift A B g ⟶ S1755Lift A B g) :=
    S1766_modification_subsingleton _ _
  exact ⟨α, β, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The extraction is constant on 2-isomorphism classes. -/
theorem S1812ModelHomOfCoverMap_eq_of_coverMapRel {A B : S1728Cover}
    {f g : S1728CoverMap A B} (h : S1728CoverMapRel f g) :
    S1755ModelHomOfCoverMap A B f = S1755ModelHomOfCoverMap A B g := by
  obtain ⟨e⟩ := h
  obtain ⟨ie⟩ := S1812LiftIsoOfMapIso (A := A) (B := B) e
  exact S1742HomOfStrongTrans_congr (F := S1726K) ie

/-- **The kernel of the S1755 extraction is exactly 2-isomorphism.**  This is the
converse of S1755CoverMapRel_of_modelHom_eq, and it needs no hypothesis. -/
theorem S1812ModelHomOfCoverMap_eq_iff_coverMapRel {A B : S1728Cover}
    (f g : S1728CoverMap A B) :
    S1755ModelHomOfCoverMap A B f = S1755ModelHomOfCoverMap A B g ↔
      S1728CoverMapRel f g :=
  ⟨S1755CoverMapRel_of_modelHom_eq, S1812ModelHomOfCoverMap_eq_of_coverMapRel⟩

/-! ## 6. The extraction is a bijection on 2-isomorphism classes -/

/-- The 2-isomorphism classes of cover maps, as a quotient type. -/
abbrev S1812CoverMapClass (A B : S1728Cover) : Type 1 :=
  Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g)

/-- The extraction descended to 2-isomorphism classes. -/
noncomputable def S1812QuotExtraction (A B : S1728Cover) :
    S1812CoverMapClass A B → S1812ModelHomOver A B :=
  Quot.lift (fun f => S1812ModelHomOfCoverMapSlice A B f)
    (fun f g hrel => Subtype.ext (S1812ModelHomOfCoverMap_eq_of_coverMapRel hrel))

/-- Computation rule of the descended extraction. -/
theorem S1812QuotExtraction_mk (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1812QuotExtraction A B (Quot.mk _ f) = S1812ModelHomOfCoverMapSlice A B f := rfl

/-- **Under the missing unit, the extraction is a bijection from 2-isomorphism
classes of cover maps onto model morphisms over the base.** -/
noncomputable def S1812QuotSliceEquiv (h : S1755SourceRetraction) (A B : S1728Cover) :
    S1812CoverMapClass A B ≃ S1812ModelHomOver A B where
  toFun := S1812QuotExtraction A B
  invFun g := Quot.mk _ (S1812ModelHomToCoverMap A B g)
  left_inv := by
    intro q
    induction q using Quot.inductionOn with
    | h f =>
      apply Quot.sound
      exact S1755CoverMapRel_of_modelHom_eq
        (S1812ModelHomOfCoverMap_toCoverMap h A B (S1812ModelHomOfCoverMapSlice A B f))
  right_inv := by
    intro g
    exact Subtype.ext (S1812ModelHomOfCoverMap_toCoverMap h A B g)

/-- In particular the descended extraction is injective and surjective. -/
theorem S1812QuotExtraction_bijective (h : S1755SourceRetraction) (A B : S1728Cover) :
    Function.Bijective (S1812QuotExtraction A B) :=
  (S1812QuotSliceEquiv h A B).bijective

/-! ## 7. Raw injectivity: the exact residual -/

/-- Raw injectivity of the extraction on a pair of covers. -/
def S1812RawInjective (A B : S1728Cover) : Prop :=
  Function.Injective (S1755ModelHomOfCoverMap A B)

/-- **Raw injectivity of the extraction is exactly discreteness of cover-map hom
types with respect to 2-isomorphism.**  This is the choice of a representative
in each 2-isomorphism class, not a statement about geometry. -/
theorem S1812RawInjective_iff_discrete :
    (∀ A B : S1728Cover, S1812RawInjective A B) ↔ S1766CoverMapDiscrete := by
  constructor
  · intro h A B f g hrel
    exact h A B ((S1812ModelHomOfCoverMap_eq_iff_coverMapRel f g).mpr hrel)
  · intro h A B f g hfg
    exact h A B f g ((S1812ModelHomOfCoverMap_eq_iff_coverMapRel f g).mp hfg)

/-- Under the missing unit, raw injectivity is exactly the statement that the
constructed inverse is a strict left inverse. -/
theorem S1812LeftInverse_of_rawInjective (h : S1755SourceRetraction)
    (hraw : ∀ A B : S1728Cover, S1812RawInjective A B)
    (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1812ModelHomToCoverMap A B (S1812ModelHomOfCoverMapSlice A B f) = f := by
  refine hraw A B ?_
  show S1755ModelHomOfCoverMap A B
      (S1812ModelHomToCoverMap A B (S1812ModelHomOfCoverMapSlice A B f)) =
    S1755ModelHomOfCoverMap A B f
  rw [S1812ModelHomOfCoverMap_toCoverMap h]
  rfl

/-- The slice equivalence, under the missing unit and raw injectivity.  This is
the two-sided inverse of the extraction in the correct hom type. -/
noncomputable def S1812SliceEquiv (h : S1755SourceRetraction)
    (hraw : ∀ A B : S1728Cover, S1812RawInjective A B) (A B : S1728Cover) :
    S1728CoverMap A B ≃ S1812ModelHomOver A B where
  toFun f := S1812ModelHomOfCoverMapSlice A B f
  invFun g := S1812ModelHomToCoverMap A B g
  left_inv f := S1812LeftInverse_of_rawInjective h hraw A B f
  right_inv g := Subtype.ext (S1812ModelHomOfCoverMap_toCoverMap h A B g)

/-- The strict two-sided inverse on the slice, as a proposition. -/
def S1812SliceBijective (A B : S1728Cover) : Prop :=
  Function.Bijective (S1812ModelHomOfCoverMapSlice A B)

/-- Raw injectivity is exactly the missing half of the slice bijectivity. -/
theorem S1812SliceBijective_iff (h : S1755SourceRetraction) (A B : S1728Cover) :
    S1812SliceBijective A B ↔ S1812RawInjective A B := by
  constructor
  · intro hbij f g hfg
    exact hbij.1 (by
      show S1812ModelHomOfCoverMapSlice A B f = S1812ModelHomOfCoverMapSlice A B g
      exact Subtype.ext hfg)
  · intro hraw
    refine ⟨fun f g hfg => hraw (congrArg Subtype.val hfg), ?_⟩
    intro g
    exact ⟨S1812ModelHomToCoverMap A B g,
      Subtype.ext (S1812ModelHomOfCoverMap_toCoverMap h A B g)⟩

/-! ## 8. The exact status of S1755ModelHomEquivMissing -/

/-- The raw two-sided inverse data, built from the slice triangle and raw
injectivity. -/
noncomputable def S1812CoverModelHomEquivDataOf (h : S1755SourceRetraction)
    (htri : ∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
      g ≫ S1733ModelOver B = S1733ModelOver A)
    (hraw : ∀ A B : S1728Cover, S1812RawInjective A B) (A B : S1728Cover) :
    S1755CoverModelHomEquivData A B where
  invFun g := S1812ModelHomToCoverMap A B ⟨g, htri A B g⟩
  left_inv f := by
    refine hraw A B ?_
    show S1755ModelHomOfCoverMap A B
        (S1812ModelHomToCoverMap A B ⟨S1755ModelHomOfCoverMap A B f, _⟩) =
      S1755ModelHomOfCoverMap A B f
    rw [S1812ModelHomOfCoverMap_toCoverMap h]
  right_inv g := S1812ModelHomOfCoverMap_toCoverMap h A B ⟨g, htri A B g⟩

/-- **S1755ModelHomEquivMissing forces every model morphism to be over the
base.**  This is the obstruction to the raw statement: its hom type is
Over (Spec F'), which is strictly larger than the slice over Spec R'. -/
theorem S1812ModelHomEquivMissing_implies_triangle (h : S1755ModelHomEquivMissing) :
    ∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
      g ≫ S1733ModelOver B = S1733ModelOver A := by
  intro A B g
  obtain ⟨d⟩ := h A B
  have h1 : S1755ModelHomOfCoverMap A B (d.invFun g) = g := d.right_inv g
  calc g ≫ S1733ModelOver B
      = S1755ModelHomOfCoverMap A B (d.invFun g) ≫ S1733ModelOver B := by rw [h1]
    _ = S1733ModelOver A := S1812ModelHomOfCoverMap_triangle A B (d.invFun g)

/-- S1755ModelHomEquivMissing also gives raw injectivity of the extraction. -/
theorem S1812RawInjective_of_modelHomEquiv (h : S1755ModelHomEquivMissing) :
    ∀ A B : S1728Cover, S1812RawInjective A B := by
  intro A B f g hfg
  obtain ⟨d⟩ := h A B
  have hf : d.invFun (S1755ModelHomOfCoverMap A B f) = f := d.left_inv f
  have hg : d.invFun (S1755ModelHomOfCoverMap A B g) = g := d.left_inv g
  rw [hfg] at hf
  rw [hg] at hf
  exact hf.symm

/-- **The exact characterization of S1755's missing statement.**  Given the
missing unit of the two-pullback, the raw two-sided inverse data on all
Over (Spec F') model morphisms is equivalent to the conjunction of

* the slice condition: every model morphism is a morphism over Spec R', and
* raw injectivity of the extraction, i.e. discreteness of cover-map hom types.

Both are genuinely absent from the S1755 extraction: the first fails for the
Over (Spec F') hom type in general, and the second is the 2-isomorphism
representative choice isolated by S1766. -/
theorem S1812ModelHomEquivMissing_iff (h : S1755SourceRetraction) :
    S1755ModelHomEquivMissing ↔
      ((∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
          g ≫ S1733ModelOver B = S1733ModelOver A) ∧
        ∀ A B : S1728Cover, S1812RawInjective A B) := by
  constructor
  · intro hm
    exact ⟨S1812ModelHomEquivMissing_implies_triangle hm,
      S1812RawInjective_of_modelHomEquiv hm⟩
  · rintro ⟨htri, hraw⟩ A B
    exact ⟨S1812CoverModelHomEquivDataOf h htri hraw A B⟩

/-- The two closed forms: on the slice the extraction is bijective under the
missing unit and raw injectivity; on all Over (Spec F') morphisms it is
bijective only if in addition every model morphism is over the base. -/
theorem S1812SliceBijective_of_rawInjective (h : S1755SourceRetraction)
    (hraw : ∀ A B : S1728Cover, S1812RawInjective A B) (A B : S1728Cover) :
    S1812SliceBijective A B :=
  (S1812SliceBijective_iff h A B).mpr (hraw A B)

/-! ## 9. Checks -/

#check S1812EvalProjectionMap
#check S1812EvalStrongTransOfHom
#check S1812ModelHomOver
#check S1812triangle_postcomp
#check S1812overTriangle_of_slice
#check S1812ModelHomOfCoverMap_triangle
#check S1812ModelHomOfCoverMapSlice
#check S1812StrongTransProj
#check S1812ModelHomToCoverMap
#check S1812LiftIsoStrongTransOfHom
#check S1812ModelHomOfCoverMap_toCoverMap
#check S1812ConeMorphism
#check S1812LiftIsoOfMapIso
#check S1812ModelHomOfCoverMap_eq_of_coverMapRel
#check S1812ModelHomOfCoverMap_eq_iff_coverMapRel
#check S1812CoverMapClass
#check S1812QuotExtraction
#check S1812QuotSliceEquiv
#check S1812QuotExtraction_bijective
#check S1812RawInjective
#check S1812RawInjective_iff_discrete
#check S1812LeftInverse_of_rawInjective
#check S1812SliceEquiv
#check S1812SliceBijective
#check S1812SliceBijective_iff
#check S1812CoverModelHomEquivDataOf
#check S1812ModelHomEquivMissing_implies_triangle
#check S1812RawInjective_of_modelHomEquiv
#check S1812ModelHomEquivMissing_iff
#check S1812SliceBijective_of_rawInjective

#print axioms S1812EvalProjectionMap
#print axioms S1812EvalStrongTransOfHom
#print axioms S1812triangle_postcomp
#print axioms S1812overTriangle_of_slice
#print axioms S1812ModelHomOfCoverMap_triangle
#print axioms S1812ModelHomToCoverMap_map
#print axioms S1812StrongTransProj
#print axioms S1812ModelHomToCoverMap
#print axioms S1812LiftIsoStrongTransOfHom
#print axioms S1812ModelHomOfCoverMap_toCoverMap
#print axioms S1812ConeMorphism
#print axioms S1812LiftIsoOfMapIso
#print axioms S1812ModelHomOfCoverMap_eq_of_coverMapRel
#print axioms S1812ModelHomOfCoverMap_eq_iff_coverMapRel
#print axioms S1812QuotExtraction
#print axioms S1812QuotSliceEquiv
#print axioms S1812QuotExtraction_bijective
#print axioms S1812RawInjective_iff_discrete
#print axioms S1812SliceEquiv
#print axioms S1812SliceBijective_iff
#print axioms S1812CoverModelHomEquivDataOf
#print axioms S1812ModelHomEquivMissing_implies_triangle
#print axioms S1812RawInjective_of_modelHomEquiv
#print axioms S1812ModelHomEquivMissing_iff

end LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual
