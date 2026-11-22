/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

/-!
# S1816: finite etale covers of the S1726 orbicurve as covers of Spec R'

## Setting

The S1726 D6 orbicurve 'S1726Orbicurve : HyperbolicOrbicurve F'' carries the
representable category-valued etale stack of the affine scheme
'S1726AffineOver = Spec R'' over 'Spec F'' (S1726RepresentableIsStack).

A finite etale cover of the orbicurve ('Iut.OrbicurveFiniteEtaleCover') is an
etale stack 'A.source' together with a map 'A.map : A.source ⟶ X.stack' which is
representably finite etale: every scheme-valued point of 'X.stack' pulls it back
to a scheme-theoretic finite etale morphism ('A.finiteEtale.baseChange',
'A.finiteEtale.hasProperty').

## What is constructed here, unconditionally

* 'S1816Obj': the object map of the wanted functor

      OrbicurveFiniteEtaleCover S1726Orbicurve ⥤ FiniteEtaleCover (Spec R').

  A cover 'A' is sent to its *affine representative*: the base change of
  'A.map' along the identity 2-Yoneda point of the representable stack of
  'Spec R'' ('A.finiteEtale.baseChange S1726AffineOver S1733BasePoint').  This is
  the affine scheme 'S1733Model A' together with the finite etale structure
  morphism 'S1733ModelOver A : S1733Model A ⟶ Spec R''.  No further choice is
  involved: the base-change presentation is a field of the cover datum.

* 'S1816Map': the action on morphisms.  A 2-isomorphism class of cover maps is
  sent to the 2-Yoneda evaluation of 'toSource_A ; f ; lift_B'
  ('S1816ModelMap'), a morphism of affine models over 'Spec R''
  ('S1816ModelMap_over').  The assignment is well defined on 2-isomorphism
  classes ('S1816ModelMap_congr').

* 'S1816Map_comp': *the composition law, unconditionally*.  The 2-Yoneda
  comparison of a composite is 2-isomorphic to the composite of the comparisons
  ('S1816EtaCompIso'); the proof only uses the **counit** 'lift ; toSource ≅ 1' of
  the identity-point two-pullback, which S1743 supplies unconditionally
  ('S1816Counit').

## The exact first missing statement

The **identity law** is not available.  At a cover 'A' it is equivalent to
'S1756End A = 1', i.e. to the missing **unit** 2-cell 'toSource ; lift ≅ 1' of the
identity-point base change ('S1816Map_id_iff', 'S1756Unit_iff_end').  This is
exactly S1756's source representability statement: the pullback of 'A.map' along
the identity 1-cell is the source stack itself.

Consequently:

* 'S1816FunctorLaw_iff_firstMissing': the canonical object and morphism maps
  satisfy the identity law for *all* covers if and only if every cover source is
  represented by its affine model ('S1756FirstMissing');
* 'S1816FunctorOf': from that statement, the functor into
  'FiniteEtaleCover (Spec R')' is constructed.

Thus the affine representative ('S1816Obj'), the finite etale structure
('S1733Model_finiteEtale'), 'finiteEtale.baseChange' and 2-Yoneda (S1742/S1743)
are all available; the single missing input is the source representability
2-cell.  Nothing else is assumed.

## Faithfulness, fullness and the equivalence criterion

* 'S1816Map_injective' / 'S1816FunctorOf_faithful': the comparison is
  **faithful, unconditionally**.  A cover map is recovered from its model
  comparison by conjugating with the free counits ('S1816ConjIso') and applying
  2-Yoneda in the sharp form 'S1756IsoIffEval'.

* 'S1816Full' / 'S1816FunctorOf_full_iff': fullness is the hom-level statement
  that every morphism of affine models over Spec R' comes from a cover map.

* 'S1816FunctorOf_isEquivalence_iff': under the missing source representability,
  the comparison is an equivalence **if and only if** it is full and essentially
  surjective.

## What is *not* claimed

No equivalence is asserted.  'S1816FunctorOf' is conditional on
'S1756FirstMissing'; fullness ('S1816Full') and essential surjectivity
('S1816EssSurj', the inverse construction "representable stack of a finite etale
cover of Spec R'") are not established here.  No sorry, no new axiom, no
Shrink/ULift/PUnit, no fake category and no fake functor is introduced.

## Axiom footprint

Only propext, Classical.choice and Quot.sound; see the #print axioms block at the
end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual.S1641Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 0. The base scheme and the target category -/

/-- The affine base Spec R' underlying the S1726 model. -/
abbrev S1816Base : Scheme := S1733BaseScheme

/-- The base of the target is the underlying scheme of the S1726 affine base. -/
theorem S1816Base_eq_left : (S1726AffineOver).left = S1816Base := rfl

/-- The base is the spectrum of the coordinate ring R'. -/
theorem S1816Base_eq_spec :
    S1816Base = Spec (CommRingCat.of S1726CoordinateRing) := rfl

/-- The target category: finite etale covers of Spec R'. -/
abbrev S1816Target : Type 1 := FiniteEtaleCover S1816Base

/-- The target is the category FiniteEtaleCover (Spec R') of S1799. -/
theorem S1816Target_eq_S1799 :
    S1816Target = FiniteEtaleCover (specBase S1726CoordinateRing) := rfl

example : Category.{0, 1} S1816Target := inferInstance

/-! ## 1. The affine representative of the source stack: the object map -/

/-- The object map.  A cover of the orbicurve is sent to the identity-point base
change of its structure map: the affine representative S1733Model A of its
source stack, with the finite etale structure morphism to Spec R' supplied by
the representable finite-etale predicate. -/
noncomputable def S1816Obj (A : S1728Cover) : S1816Target :=
  FiniteEtaleCover.mk (S := S1816Base) (S1733ModelOver A).left
    (S1733Model_finiteEtale A).2 (S1733Model_finiteEtale A).1

/-- The carrier of the attached cover is the affine model of the source. -/
@[simp] theorem S1816Obj_carrier (A : S1728Cover) :
    FiniteEtaleCover.carrier (S1816Obj A) = (S1733Model A).left := rfl

/-- The structure morphism of the attached cover is the base-change projection. -/
@[simp] theorem S1816Obj_structureMap (A : S1728Cover) :
    FiniteEtaleCover.structureMap (S1816Obj A) = (S1733ModelOver A).left := rfl

/-- The attached cover is a finite etale cover of Spec R'. -/
theorem S1816Obj_finiteEtale (A : S1728Cover) :
    IsFiniteEtaleHom (FiniteEtaleCover.structureMap (S1816Obj A)) :=
  ⟨(S1733Model_finiteEtale A).2, (S1733Model_finiteEtale A).1⟩

/-! ## 2. Bicategorical calculus: inserting a comparison in the middle -/

section BicategoryCalculus

variable {W X Y Z D : EtaleStackPseudofunctor S1726K}

/-- Inserting a 2-isomorphism u ; v ≅ 1 in the middle of a composite
(p ; u) ; ((v ; q) ; r). -/
noncomputable def S1816Insert
    (p : Pseudofunctor.StrongTrans W X) (u : Pseudofunctor.StrongTrans X Y)
    (v : Pseudofunctor.StrongTrans Y X) (q : Pseudofunctor.StrongTrans X Z)
    (r : Pseudofunctor.StrongTrans Z D)
    (h : Iso (Pseudofunctor.StrongTrans.vcomp u v)
      (Pseudofunctor.StrongTrans.id X)) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp p u)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp v q) r))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp p q) r) :=
  (S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp p u)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp v q) r)
      (Pseudofunctor.StrongTrans.vcomp v (Pseudofunctor.StrongTrans.vcomp q r))
      (S1756AssociatorIso v q r)).trans
    ((S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp p u) v
        (Pseudofunctor.StrongTrans.vcomp q r)).symm.trans
      ((S1756WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp p u) v)
          (Pseudofunctor.StrongTrans.vcomp p (Pseudofunctor.StrongTrans.vcomp u v))
          (Pseudofunctor.StrongTrans.vcomp q r) (S1756AssociatorIso p u v)).trans
        ((S1756WhiskerRightIso
            (Pseudofunctor.StrongTrans.vcomp p (Pseudofunctor.StrongTrans.vcomp u v))
            (Pseudofunctor.StrongTrans.vcomp p (Pseudofunctor.StrongTrans.id X))
            (Pseudofunctor.StrongTrans.vcomp q r)
            (S1756WhiskerLeftIso p (Pseudofunctor.StrongTrans.vcomp u v)
              (Pseudofunctor.StrongTrans.id X) h)).trans
          ((S1756WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp p (Pseudofunctor.StrongTrans.id X)) p
              (Pseudofunctor.StrongTrans.vcomp q r)
              (S1756RightUnitorIso p)).trans
            ((S1756AssociatorIso p q r).symm)))))

end BicategoryCalculus

/-! ## 3. The affine model morphism of a cover map -/

/-- The comparison 2-cell of a cover map: the comparison of the source, the
cover map itself, and the lift of the target. -/
noncomputable def S1816Eta (A B : S1728Cover) (f : S1728CoverMap A B) :
    Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) (S1743Y (S1733Model B)) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) (S1743Lift B)

/-- The affine model morphism attached to a cover map: the 2-Yoneda evaluation
of the comparison.  This is S1781's S1781ModelMap, restated in evaluation form
so that the functor laws can be stated directly. -/
noncomputable def S1816ModelMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1733Model A ⟶ S1733Model B :=
  S1743YonedaEval (S1733Model A) (S1733Model B) (S1816Eta A B f)

/-- The model morphism is the 2-Yoneda evaluation of the comparison. -/
theorem S1816ModelMap_eq_eval (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1816ModelMap A B f =
      S1743YonedaEval (S1733Model A) (S1733Model B) (S1816Eta A B f) := rfl

/-- The counit of the identity-point two-pullback: lift ; toSource ≅ 1.
This half of the equivalence is unconditional (S1743). -/
noncomputable def S1816Counit (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
  (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)

/-- The lift projects to the structure map of the cover. -/
noncomputable def S1816LiftProjection (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A))
      A.map :=
  (S1743BaseChange A).isPullback.liftToY (S1743Source A) (S1743IdentityCone A)

/-- The comparison of a cover map is compatible with the projections to the base
scheme. -/
noncomputable def S1816EtaProjection (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1756ProjectionMap B))
      (S1756ProjectionMap A) :=
  (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
      (S1743Lift B) (S1756ProjectionMap B)).trans
    ((S1756WhiskerLeftIso _ _ _ (S1816LiftProjection B)).trans
    ((S1756AssociatorIso (S1756ToSource A) f.map B.map).trans
    ((S1756WhiskerLeftIso (S1756ToSource A) _ _ f.commutes).trans
    ((S1743BaseChange A).commutes.trans
      (S1756RightUnitorIso (S1756ProjectionMap A))))))

/-- The affine model morphism is a morphism over the base, at the level of
S1756's structure morphism S1756Projection. -/
theorem S1816ModelMap_over_projection (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1816ModelMap A B f ≫ S1756Projection B = S1756Projection A := by
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) S1726AffineOver
    (S1816Eta A B f) (S1756ProjectionMap B)
  have hcongr : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1756ProjectionMap B)) =
      S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) :=
    S1743YonedaEval_congr_iso (S1733Model A) S1726AffineOver (S1816EtaProjection A B f)
  calc
    S1816ModelMap A B f ≫ S1756Projection B
        = S1743YonedaEval (S1733Model A) (S1733Model B) (S1816Eta A B f) ≫
            S1743YonedaEval (S1733Model B) S1726AffineOver (S1756ProjectionMap B) := by
          rw [S1756YonedaEval_projectionMap B]
          rfl
    _ = S1743YonedaEval (S1733Model A) S1726AffineOver
          (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1756ProjectionMap B)) :=
          hcomp.symm
    _ = S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) := hcongr
    _ = S1756Projection A := S1756YonedaEval_projectionMap A

/-- The affine model morphism is a morphism over the base Spec R'. -/
theorem S1816ModelMap_over (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1816ModelMap A B f ≫ S1733ModelOver B = S1733ModelOver A :=
  S1816ModelMap_over_projection A B f

/-- The base compatibility on underlying scheme morphisms. -/
theorem S1816ModelMap_over_left (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1816ModelMap A B f).left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left :=
  congrArg Over.Hom.left (S1816ModelMap_over A B f)

/-- The model morphism depends only on the 2-isomorphism class of the cover map. -/
theorem S1816ModelMap_congr (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) : S1816ModelMap A B f = S1816ModelMap A B g := by
  apply S1742HomOfStrongTrans_congr
  exact S1756WhiskerRightIso _ _ (S1743Lift B)
    (S1756WhiskerLeftIso (S1756ToSource A) _ _ h.some)

/-- The model morphism of the identity cover map is S1756's self-endomorphism
S1756End, the only obstruction to the identity law. -/
theorem S1816ModelMap_id_class (A : S1728Cover) :
    S1816ModelMap A A (S1641CoverMapId A) = S1756End A := by
  apply S1742HomOfStrongTrans_congr
  change Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1641CoverMapId A).map)
      (S1743Lift A))
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
  rw [S1641CoverMapId_map]
  exact S1756WhiskerRightIso _ _ (S1743Lift A) (S1756RightUnitorIso (S1756ToSource A))

/-- The comparison of a composite cover map is 2-isomorphic to the composite of
the comparisons.  The proof only uses the unconditional counit
lift ; toSource ≅ 1. -/
noncomputable def S1816EtaCompIso (A B C : S1728Cover)
    (f : S1728CoverMap A B) (g : S1728CoverMap B C) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
            (Pseudofunctor.StrongTrans.vcomp f.map g.map)) (S1743Lift C))
        (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1816Eta B C g)) := by
  show Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
            (Pseudofunctor.StrongTrans.vcomp f.map g.map)) (S1743Lift C))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) (S1743Lift B))
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource B) g.map) (S1743Lift C)))
  exact ((S1816Insert
      (p := Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
      (u := S1743Lift B) (v := S1756ToSource B) (q := g.map) (r := S1743Lift C)
      (S1816Counit B)).trans
    (S1756WhiskerRightIso _ _ (S1743Lift C)
      (S1756AssociatorIso (S1756ToSource A) f.map g.map))).symm

/-- The affine model morphisms are compatible with composition. -/
theorem S1816ModelMap_comp (A B C : S1728Cover)
    (f : S1728CoverMap A B) (g : S1728CoverMap B C) :
    S1816ModelMap A C (S1641CoverMapComp f g) =
      S1816ModelMap A B f ≫ S1816ModelMap B C g := by
  show S1743YonedaEval (S1733Model A) (S1733Model C)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp f.map g.map)) (S1743Lift C)) =
    S1743YonedaEval (S1733Model A) (S1733Model B) (S1816Eta A B f) ≫
      S1743YonedaEval (S1733Model B) (S1733Model C) (S1816Eta B C g)
  rw [← S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) (S1733Model C)
    (S1816Eta A B f) (S1816Eta B C g)]
  exact S1743YonedaEval_congr_iso (S1733Model A) (S1733Model C)
    (S1816EtaCompIso A B C f g)

/-! ## 4. The action on 2-isomorphism classes of cover maps -/

/-- The forgetful functor to schemes over the base, written as an abbrev so that
its faithful instance is found by typeclass inference. -/
abbrev S1816Forget : S1816Target ⥤ Over S1816Base :=
  ObjectProperty.ι (fun X : Over S1816Base => IsFiniteEtaleHom X.hom)

/-- The underlying morphism of the target associated with a cover map.  The model
morphism is already a morphism of the two underlying schemes over the common
base Spec R'. -/
noncomputable def S1816OverMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1816Obj A).obj ⟶ (S1816Obj B).obj := by
  refine Over.homMk (f := ?_) ?_
  · change (S1733Model A).left ⟶ (S1733Model B).left
    exact (S1816ModelMap A B f).left
  · change (S1816ModelMap A B f).left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left
    exact S1816ModelMap_over_left A B f

/-- The cover morphism attached to a cover map. -/
noncomputable def S1816MapOfCoverMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1816Obj A ⟶ S1816Obj B :=
  InducedCategory.homMk (S1816OverMap A B f)

/-- The underlying morphism of the attached cover morphism. -/
theorem S1816MapOfCoverMap_hom (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1816MapOfCoverMap A B f).hom = S1816OverMap A B f := rfl

/-- The underlying scheme morphism of the attached cover morphism. -/
@[simp] theorem S1816MapOfCoverMap_hom_left (A B : S1728Cover)
    (f : S1728CoverMap A B) :
    (S1816MapOfCoverMap A B f).hom.left = (S1816ModelMap A B f).left := by
  rfl

/-- The underlying morphism of a composite of attached cover morphisms. -/
theorem S1816_hom_comp (A B C : S1728Cover) (f : S1816Obj A ⟶ S1816Obj B)
    (g : S1816Obj B ⟶ S1816Obj C) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The attached cover morphism depends only on the 2-isomorphism class. -/
theorem S1816MapOfCoverMap_congr (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) : S1816MapOfCoverMap A B f = S1816MapOfCoverMap A B g := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [S1816MapOfCoverMap_hom_left, S1816MapOfCoverMap_hom_left, S1816ModelMap_congr A B h]

/-- The action on 2-isomorphism classes of cover maps. -/
noncomputable def S1816Map (A B : S1728Cover) : (A ⟶ B) → (S1816Obj A ⟶ S1816Obj B) :=
  Quot.lift (S1816MapOfCoverMap A B) (fun _ _ h => S1816MapOfCoverMap_congr A B h)

/-- The class-level action is the model comparison on representatives. -/
@[simp] theorem S1816Map_mk (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1816Map A B (Quot.mk _ f) = S1816MapOfCoverMap A B f := rfl

/-- The composition law is unconditional. -/
theorem S1816Map_comp (A B C : S1728Cover) (f : A ⟶ B) (g : B ⟶ C) :
    S1816Map A C (f ≫ g) = S1816Map A B f ≫ S1816Map B C g := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      show S1816MapOfCoverMap A C (S1641CoverMapComp f g) =
        S1816MapOfCoverMap A B f ≫ S1816MapOfCoverMap B C g
      apply S1816Forget.map_injective
      show (S1816MapOfCoverMap A C (S1641CoverMapComp f g)).hom =
        (S1816MapOfCoverMap A B f ≫ S1816MapOfCoverMap B C g).hom
      rw [S1816_hom_comp]
      apply Over.OverMorphism.ext
      rw [S1816MapOfCoverMap_hom_left, Over.comp_left,
        S1816MapOfCoverMap_hom_left, S1816MapOfCoverMap_hom_left]
      show (S1816ModelMap A C (S1641CoverMapComp f g)).left =
        (S1816ModelMap A B f).left ≫ (S1816ModelMap B C g).left
      rw [S1816ModelMap_comp]
      rfl

/-! ## 5. The identity law is exactly the missing source representability -/

/-- The identity arrow of an attached cover, transported to the ambient
Over-category through the forgetful functor. -/
theorem S1816_id_hom (A : S1728Cover) :
    S1816Forget.map (𝟙 (S1816Obj A)) = 𝟙 ((S1816Obj A).obj) := rfl

/-- **The identity law at a cover is the missing source-representability statement.**
It is equivalent to S1756's scheme-level equation S1756End A = 1, i.e. to the
unit 2-cell toSource ; lift ≅ 1. -/
theorem S1816Map_id_iff (A : S1728Cover) :
    S1816Map A A (𝟙 A) = 𝟙 (S1816Obj A) ↔ S1756End A = 𝟙 (S1733Model A) := by
  have key : S1816Map A A (𝟙 A) = S1816MapOfCoverMap A A (S1641CoverMapId A) := rfl
  rw [key]
  constructor
  · intro h
    have h2 : (S1816MapOfCoverMap A A (S1641CoverMapId A)).hom =
        𝟙 ((S1816Obj A).obj) := by
      have h3 : S1816Forget.map (S1816MapOfCoverMap A A (S1641CoverMapId A)) =
          S1816Forget.map (𝟙 (S1816Obj A)) := congrArg S1816Forget.map h
      rw [S1816_id_hom] at h3
      exact h3
    have h4 : (S1816MapOfCoverMap A A (S1641CoverMapId A)).hom.left =
        𝟙 ((S1816Obj A).obj.left) := by
      rw [h2, Over.id_left]
    rw [S1816MapOfCoverMap_hom_left] at h4
    rw [S1816ModelMap_id_class] at h4
    exact Over.OverMorphism.ext h4
  · intro h
    apply S1816Forget.map_injective
    rw [S1816_id_hom]
    apply Over.OverMorphism.ext
    show (S1816MapOfCoverMap A A (S1641CoverMapId A)).hom.left =
      𝟙 ((S1816Obj A).obj.left)
    rw [S1816MapOfCoverMap_hom_left, S1816ModelMap_id_class, h, Over.id_left]
    rfl

/-- The identity law is the missing unit 2-cell of the identity-point base change. -/
theorem S1816Map_id_iff_unit (A : S1728Cover) :
    S1816Map A A (𝟙 A) = 𝟙 (S1816Obj A) ↔ S1756Unit A :=
  (S1816Map_id_iff A).trans (S1756Unit_iff_end A).symm

/-- The canonical object and morphism maps satisfy the identity law for every
cover if and only if every cover source is represented by its affine model. -/
theorem S1816FunctorLaw_iff_firstMissing :
    (∀ A : S1728Cover, S1816Map A A (𝟙 A) = 𝟙 (S1816Obj A)) ↔ S1756FirstMissing :=
  ⟨fun h A => (S1816Map_id_iff A).mp (h A), fun h A => (S1816Map_id_iff A).mpr (h A)⟩

/-- The identity law at one cover follows from the first missing statement. -/
theorem S1816Map_id_of_firstMissing (h : S1756FirstMissing) (A : S1728Cover) :
    S1816Map A A (𝟙 A) = 𝟙 (S1816Obj A) :=
  (S1816Map_id_iff A).mpr (h A)

/-! ## 6. Faithfulness of the comparison -/

/-- The cover map is 2-isomorphic to the conjugate of its model comparison by the
two lifts.  Only the unconditional counits lift ; toSource ≅ 1 are used. -/
noncomputable def S1816ConjIso (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso f.map (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
      (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1756ToSource B))) :=
  (S1756LeftUnitorIso f.map).symm.trans
    ((S1756WhiskerRightIso
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
        (Pseudofunctor.StrongTrans.id (S1743Source A)) f.map
        (S1816Counit A)).symm.trans
      ((S1756AssociatorIso (S1743Lift A) (S1756ToSource A) f.map).trans
        ((S1756WhiskerLeftIso (S1743Lift A)
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
            (Pseudofunctor.StrongTrans.vcomp
              (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
              (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1756ToSource B)))
            ((S1756RightUnitorIso
                (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)).symm.trans
              (S1756WhiskerLeftIso
                (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
                (Pseudofunctor.StrongTrans.id (S1743Source B))
                (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1756ToSource B))
                (S1816Counit B).symm))).trans
          ((S1756WhiskerLeftIso (S1743Lift A)
              (Pseudofunctor.StrongTrans.vcomp
                (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
                (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1756ToSource B)))
              (Pseudofunctor.StrongTrans.vcomp
                (Pseudofunctor.StrongTrans.vcomp
                  (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
                  (S1743Lift B))
                (S1756ToSource B))
              (S1756AssociatorIso
                (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
                (S1743Lift B) (S1756ToSource B)).symm)))))

/-- **The comparison is injective on 2-isomorphism classes of cover maps.**  This
is unconditional: a cover map is recovered from its model comparison by
conjugating with the free counits and applying 2-Yoneda. -/
theorem S1816Map_injective (A B : S1728Cover) :
    Function.Injective (S1816Map A B) := by
  intro f g h
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      apply Quot.sound
      have h' : S1816MapOfCoverMap A B f = S1816MapOfCoverMap A B g := h
      have h1 : (S1816ModelMap A B f).left = (S1816ModelMap A B g).left := by
        have h2 : (S1816MapOfCoverMap A B f).hom.left =
            (S1816MapOfCoverMap A B g).hom.left := by
          rw [h']
        rwa [S1816MapOfCoverMap_hom_left, S1816MapOfCoverMap_hom_left] at h2
      have h3 : S1816ModelMap A B f = S1816ModelMap A B g := Over.OverMorphism.ext h1
      have h4 : Nonempty (S1816Eta A B f ≅ S1816Eta A B g) :=
        (S1756IsoIffEval (S1733Model A) (S1733Model B) _ _).mpr h3
      obtain ⟨e⟩ := h4
      exact ⟨(S1816ConjIso A B f).trans
        ((S1756WhiskerLeftIso (S1743Lift A)
            (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B f) (S1756ToSource B))
            (Pseudofunctor.StrongTrans.vcomp (S1816Eta A B g) (S1756ToSource B))
            (S1756WhiskerRightIso (S1816Eta A B f) (S1816Eta A B g)
              (S1756ToSource B) e)).trans
          (S1816ConjIso A B g).symm)⟩

/-- Fullness of the comparison: every morphism of affine models over Spec R' comes
from a cover map.  This is the 2-Yoneda comparison on hom categories; it is not
established here. -/
def S1816Full : Prop := ∀ (A B : S1728Cover), Function.Surjective (S1816Map A B)

/-! ## 7. The functor, conditional on source representability -/

/-- The comparison functor OrbicurveFiniteEtaleCover S1726Orbicurve ⥤
FiniteEtaleCover (Spec R') from the source-representability statement. -/
noncomputable def S1816FunctorOf (h : S1756FirstMissing) :
    S1728Cover ⥤ S1816Target where
  obj := S1816Obj
  map {A B} := S1816Map A B
  map_id A := S1816Map_id_of_firstMissing h A
  map_comp {A B C} f g := S1816Map_comp A B C f g

/-- The object map of the conditional functor is the affine representative. -/
@[simp] theorem S1816FunctorOf_obj (h : S1756FirstMissing) (A : S1728Cover) :
    (S1816FunctorOf h).obj A = S1816Obj A := rfl

/-- The morphism map of the conditional functor is the 2-Yoneda comparison. -/
@[simp] theorem S1816FunctorOf_map (h : S1756FirstMissing) {A B : S1728Cover}
    (f : A ⟶ B) : (S1816FunctorOf h).map f = S1816Map A B f := rfl

/-! ## 8. What an equivalence would still need -/

/-- Essential surjectivity of the comparison, stated without choosing the
functor: every finite etale cover of Spec R' is the affine model of a cover of
the orbicurve.  This is the inverse construction (the representable stack of a
finite etale cover of the base, with its finite etale map to the stack of
Spec R'); it is not constructed here. -/
def S1816EssSurj : Prop :=
  ∀ C : S1816Target, ∃ A : S1728Cover, Nonempty (S1816Obj A ≅ C)

/-- Essential surjectivity of the conditional functor is exactly the geometric
statement S1816EssSurj. -/
theorem S1816FunctorOf_essSurj_iff (h : S1756FirstMissing) :
    (S1816FunctorOf h).EssSurj ↔ S1816EssSurj := by
  constructor
  · intro hE C
    obtain ⟨A, ⟨e⟩⟩ := hE.mem_essImage C
    exact ⟨A, ⟨e⟩⟩
  · intro hE
    exact ⟨fun C => hE C⟩

/-- **The conditional functor is faithful, unconditionally.** -/
instance S1816FunctorOf_faithful (h : S1756FirstMissing) :
    (S1816FunctorOf h).Faithful where
  map_injective {A B} f g hfg := S1816Map_injective A B hfg

/-- Fullness of the conditional functor is the hom-level statement S1816Full. -/
theorem S1816FunctorOf_full_iff (h : S1756FirstMissing) :
    (S1816FunctorOf h).Full ↔ S1816Full := by
  constructor
  · intro hF A B φ
    obtain ⟨f, hf⟩ := hF.map_surjective φ
    exact ⟨f, hf⟩
  · intro hF
    refine ⟨fun {A B} φ => ?_⟩
    obtain ⟨f, hf⟩ := hF A B φ
    exact ⟨f, hf⟩

/-- **An equivalence is exactly fullness plus essential surjectivity**, given the
missing source representability: faithfulness is available unconditionally. -/
theorem S1816FunctorOf_isEquivalence_iff (h : S1756FirstMissing) :
    (S1816FunctorOf h).IsEquivalence ↔ (S1816FunctorOf h).Full ∧ S1816EssSurj := by
  constructor
  · intro hE
    exact ⟨hE.full, (S1816FunctorOf_essSurj_iff h).mp hE.essSurj⟩
  · rintro ⟨hfull, hess⟩
    exact ⟨inferInstance, hfull, (S1816FunctorOf_essSurj_iff h).mpr hess⟩

/-! ## 9. Checks and axiom footprint -/

#check S1816Obj
#check S1816ModelMap
#check S1816ModelMap_over
#check S1816ModelMap_comp
#check S1816Map
#check S1816Map_comp
#check S1816Map_id_iff
#check S1816FunctorLaw_iff_firstMissing
#check S1816FunctorOf
#check S1816EssSurj
#check S1816FunctorOf_essSurj_iff
#check S1816ConjIso
#check S1816Map_injective
#check S1816FunctorOf_faithful
#check S1816Full
#check S1816FunctorOf_full_iff
#check S1816FunctorOf_isEquivalence_iff

#print axioms S1816Obj
#print axioms S1816ModelMap_over
#print axioms S1816ModelMap_comp
#print axioms S1816Map_comp
#print axioms S1816Map_id_iff
#print axioms S1816FunctorLaw_iff_firstMissing
#print axioms S1816FunctorOf
#print axioms S1816Map_injective
#print axioms S1816FunctorOf_isEquivalence_iff

end LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
