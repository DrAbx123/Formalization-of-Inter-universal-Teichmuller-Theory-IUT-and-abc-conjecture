/-
# S1755: the S1742 2-Yoneda comparison applied to the S1733 cover models

## Question

S1733 chose, for every actual finite-etale cover A of the S1726 D6 orbicurve,
an affine finite-etale base-change model S1733Model A over Spec R', and
isolated two missing statements: affine cover-model data with a bijection
between model scheme morphisms and actual cover maps, and an equivalence
between the S1728 2-iso cover category and the affine finite-etale slice.

This file attacks the direct route with the S1742 2-Yoneda comparison.

## Result

For A B : S1728Cover and a cover map f : S1728CoverMap A B, the file
constructs unconditionally:

* S1755Cone f, a cone over the identity-point base-change square of B with
  apex the representable stack of the model of A;
* S1755Lift f, its lift through the two-pullback universal property;
* S1755ModelHomOfCoverMap f : S1733Model A ⟶ S1733Model B, the underlying
  scheme morphism extracted from that lift by S1742HomOfStrongTrans.

Thus the morphism action called R1 in S1744 is unconditional.  No
representability of the cover source stack is assumed: only the chosen
base-change presentation, which is part of the finite-etale structure.

The extraction is faithful on 2-isomorphism classes
(S1755CoverMapRel_of_modelHom_eq): equal extracted model morphisms force the
cover maps to be 2-isomorphic.  The proof uses the retraction half of the model
section lifted from the identity cone, which is unconditional.

The affine slice object of a cover is also constructed
unconditionally (S1755SliceObject): Spec of the model, with its finite-etale
structure morphism.  The exact missing slice comparison is packaged as
S1755SliceComparison, and is shown equivalent to S1733CoverSliceEquivalence
(S1755SliceFunctorMissing_iff).

## Exact missing statements

The raw comparison targeted by S1733AffineCoverModel is isolated as
S1755ModelHomEquivMissing: two-sided inverse data for the extraction on every
pair of covers.  It is equivalent to bijectivity of the extraction
(S1755ModelHomEquivMissing_iff_bijective), and supplies S1733's affine
cover-model missing theorem (S1755AffineCoverModelMissing_of_modelHomEquiv),
hence S1728SmallRawCoverDataRequired and a genuine Category.{0,1} on the
actual cover type.

The second half is the geometric input.  S1755SourceRetraction is the missing
other half of stack representability of a cover source by its affine model;
it is equivalent to the concrete two-sided invertibility of the chosen
base-change comparison against the chosen model section lift
(S1755SourceRetraction_iff_modelRetraction), and to full stack
representability of all cover sources
(S1755SourceRetraction_iff_representableAll).  The opposite composite is
proved unconditionally (S1755ModelSection).  S1755SourceRetraction is not
proved here.

No equivalence is asserted: the file proves the extraction and its
faithfulness on 2-isomorphism classes, and reduces the two S1733 missing
statements to precise inputs, but does not construct the inverse data or the
missing representability.

## Honest boundary

No sorry, no axiom, no Shrink, no ULift, no PUnit.  Only propext,
Classical.choice and Quot.sound are used.  The target
OrbicurveEtaleFundamentalGroup is not constructed.
-/

import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Equivalence

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual

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

/-! ## 1. The setting -/

/-- The representable etale pseudofunctor of a scheme over the S1726 field. -/
noncomputable abbrev S1755Y (S : SchemeOverField S1726K) :
    EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

/-- The source pseudofunctor of a cover. -/
abbrev S1755Source (A : S1728Cover) : EtaleStackPseudofunctor S1726K :=
  A.source.fiber

/-- The identity-point base-change presentation of a cover, i.e. the
presentation singled out by S1733. -/
noncomputable def S1755BaseChange (A : S1728Cover) :
    EtaleStackBaseChangePresentation A.map S1726AffineOver S1733BasePoint :=
  A.finiteEtale.baseChange S1726AffineOver S1733BasePoint

/-- The representable pseudofunctor of the S1733 affine model of a cover. -/
noncomputable abbrev S1755ModelStack (A : S1728Cover) :
    EtaleStackPseudofunctor S1726K :=
  S1755Y (S1755BaseChange A).pullbackScheme

/-- The two-commutative square of the identity-point base change. -/
noncomputable def S1755Square (A : S1728Cover) :
    EtalePseudofunctorSquare (S1755ModelStack A) (S1755Source A)
      (S1755Y S1726AffineOver) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S1755BaseChange A).toSource
    (S1755BaseChange A).projectionMap.transformation A.map S1733BasePoint
    (S1755BaseChange A).commutes

/-! ## 2. From a cover map to a strong transformation of the models -/

/-- The commuting 2-cell of the cone over the identity-point square of B
attached to a cover map f : A ⟶ B. -/
noncomputable def S1755ConeCommutes (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource f.map) B.map)
      (Pseudofunctor.StrongTrans.vcomp
        (S1755BaseChange A).projectionMap.transformation S1733BasePoint) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let W : Bicat := S1755ModelStack A
  let X : Bicat := S1755Source A
  let Y : Bicat := S1755Source B
  let Z : Bicat := S1726Orbicurve.stack.fiber
  let a : W ⟶ X := (S1755BaseChange A).toSource
  let b : X ⟶ Y := f.map
  let c : Y ⟶ Z := B.map
  let amap : X ⟶ Z := A.map
  let d : W ⟶ S1755Y S1726AffineOver := (S1755BaseChange A).projectionMap.transformation
  let e : S1755Y S1726AffineOver ⟶ Z := S1733BasePoint
  have hbc : a ≫ amap ≅ d ≫ e := (S1755BaseChange A).commutes
  exact (Bicategory.associator a b c) ≪≫ (Bicategory.whiskerLeftIso a f.commutes) ≪≫ hbc

/-- The cone over the identity-point square of B attached to a cover map. -/
noncomputable def S1755Cone (A B : S1728Cover) (f : S1728CoverMap A B) :
    (S1755Square B).Cone (S1755ModelStack A) where
  toX := Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource f.map
  toY := (S1755BaseChange A).projectionMap.transformation
  commutes := S1755ConeCommutes A B f

/-- The lift of the cone through the two-pullback universal property. -/
noncomputable def S1755Lift (A B : S1728Cover) (f : S1728CoverMap A B) :
    Pseudofunctor.StrongTrans (S1755ModelStack A) (S1755ModelStack B) :=
  (S1755BaseChange B).isPullback.lift (S1755ModelStack A) (S1755Cone A B f)

/-- Agreement of the lift with the first leg of the cone. -/
noncomputable def S1755Lift_toX (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755Lift A B f)
        (S1755BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource f.map) :=
  (S1755BaseChange B).isPullback.liftToX (S1755ModelStack A) (S1755Cone A B f)

/-- Agreement of the lift with the second leg of the cone. -/
noncomputable def S1755Lift_toY (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755Lift A B f)
        (S1755BaseChange B).projectionMap.transformation)
      ((S1755BaseChange A).projectionMap.transformation) :=
  (S1755BaseChange B).isPullback.liftToY (S1755ModelStack A) (S1755Cone A B f)

/-- The underlying scheme morphism of a cover map, extracted from the lifted
strong transformation by S1742's reverse 2-Yoneda comparison. -/
noncomputable def S1755ModelHomOfCoverMap (A B : S1728Cover)
    (f : S1728CoverMap A B) : S1733Model A ⟶ S1733Model B :=
  S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f)

/-- The defining computation rule of the extraction. -/
theorem S1755ModelHomOfCoverMap_def (A B : S1728Cover)
    (f : S1728CoverMap A B) :
    S1755ModelHomOfCoverMap A B f =
      S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f) := rfl

/-! ## 3. The model section and faithfulness of the extraction -/

/-- The identity cone over the square of a cover: the cover maps to itself. -/
noncomputable def S1755IdentityCone (A : S1728Cover) :
    (S1755Square A).Cone (S1755Source A) where
  toX := Pseudofunctor.StrongTrans.id (S1755Source A)
  toY := A.map
  commutes :=
    (Pseudofunctor.StrongTrans.leftUnitor A.map) ≪≫
      (Pseudofunctor.StrongTrans.rightUnitor A.map).symm

/-- The lift of the identity cone: a strong transformation from the cover
source to the representable stack of its model. -/
noncomputable def S1755ModelSectionLift (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1755Source A) (S1755ModelStack A) :=
  (S1755BaseChange A).isPullback.lift (S1755Source A) (S1755IdentityCone A)

/-- The model section is a retraction of the base-change comparison: the
composite to the cover source is 2-isomorphic to the identity. -/
noncomputable def S1755ModelSection (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755ModelSectionLift A)
        (S1755BaseChange A).toSource)
      (Pseudofunctor.StrongTrans.id (S1755Source A)) :=
  (S1755BaseChange A).isPullback.liftToX (S1755Source A) (S1755IdentityCone A)

/-- Two strong transformations of representable stacks with the same 2-Yoneda
evaluation are 2-isomorphic. -/
noncomputable def S1755IsoOfEvalEq {S T : SchemeOverField S1726K}
    (L L' : Pseudofunctor.StrongTrans (S1755Y S) (S1755Y T))
    (h : S1742HomOfStrongTrans (F := S1726K) L =
      S1742HomOfStrongTrans (F := S1726K) L') : L ≅ L' :=
  (S1742StrongTransIsoOfHom (F := S1726K) L).symm ≪≫
    eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) h) ≪≫
      (S1742StrongTransIsoOfHom (F := S1726K) L')

/-- Faithfulness on 2-isomorphism classes: a cover map whose extracted model
morphism agrees with that of another cover map is 2-isomorphic to it. -/
theorem S1755CoverMapRel_of_modelHom_eq {A B : S1728Cover}
    {f g : S1728CoverMap A B}
    (h : S1755ModelHomOfCoverMap A B f = S1755ModelHomOfCoverMap A B g) :
    S1728CoverMapRel f g := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let WA : Bicat := S1755ModelStack A
  let WB : Bicat := S1755ModelStack B
  let X : Bicat := S1755Source A
  let Y : Bicat := S1755Source B
  let a : WA ⟶ X := (S1755BaseChange A).toSource
  let aB : WB ⟶ Y := (S1755BaseChange B).toSource
  let Lf : WA ⟶ WB := S1755Lift A B f
  let Lg : WA ⟶ WB := S1755Lift A B g
  let bmap : X ⟶ Y := f.map
  let gmap : X ⟶ Y := g.map
  let sec : X ⟶ WA := S1755ModelSectionLift A
  have h' : S1742HomOfStrongTrans (F := S1726K) Lf =
      S1742HomOfStrongTrans (F := S1726K) Lg := h
  have eLift : Lf ≅ Lg := S1755IsoOfEvalEq Lf Lg h'
  have Hf : (Lf ≫ aB) ≅ (a ≫ bmap) := S1755Lift_toX A B f
  have Hg : (Lg ≫ aB) ≅ (a ≫ gmap) := S1755Lift_toX A B g
  have e1 : a ≫ bmap ≅ a ≫ gmap :=
    Hf.symm ≪≫ Bicategory.whiskerRightIso eLift aB ≪≫ Hg
  have e2 : (sec ≫ a) ≫ bmap ≅ (sec ≫ a) ≫ gmap :=
    Bicategory.associator sec a bmap ≪≫ Bicategory.whiskerLeftIso sec e1 ≪≫
      (Bicategory.associator sec a gmap).symm
  have eSec : (sec ≫ a) ≅ 𝟙 X := S1755ModelSection A
  have e3 : ((sec ≫ a) ≫ bmap) ≅ bmap :=
    Bicategory.whiskerRightIso eSec bmap ≪≫ Bicategory.leftUnitor bmap
  have e4 : ((sec ≫ a) ≫ gmap) ≅ gmap :=
    Bicategory.whiskerRightIso eSec gmap ≪≫ Bicategory.leftUnitor gmap
  exact ⟨e3.symm ≪≫ e2 ≪≫ e4⟩


/-! ## 4. The affine slice object of a cover -/

/-- The S1733 model of a cover is affine: it is finite over the affine base. -/
theorem S1755Model_isAffine (A : S1728Cover) : IsAffine (S1733Model A).left := by
  haveI : IsAffineHom (S1733ModelOver A).left :=
    (S1733Model_finiteEtale A).1.toIsAffineHom
  haveI : IsAffine (S1726AffineOver).left := inferInstanceAs (IsAffine S1726AffineScheme)
  exact isAffine_of_isAffineHom (S1733ModelOver A).left

/-- The ring whose spectrum is the affine model. -/
noncomputable abbrev S1755ModelRing (A : S1728Cover) : CommRingCatᵒᵖ :=
  Opposite.op ((S1733Model A).left.presheaf.obj (Opposite.op ⊤))

/-- The structure morphism of the affine model, written from Spec Γ(model). -/
noncomputable def S1755ModelHom (A : S1728Cover) :
    Scheme.Spec.obj (S1755ModelRing A) ⟶ S1733BaseScheme :=
  haveI : IsAffine (S1733Model A).left := S1755Model_isAffine A
  (Scheme.isoSpec (S1733Model A).left).inv ≫ (S1733ModelOver A).left

/-- The structure morphism is finite and etale. -/
theorem S1755ModelHom_finiteEtale (A : S1728Cover) :
    S1733FiniteEtale (S1755ModelHom A) := by
  haveI hA : IsAffine (S1733Model A).left := S1755Model_isAffine A
  have hfin : IsFinite (S1733ModelOver A).left := (S1733Model_finiteEtale A).1
  have het : Etale (S1733ModelOver A).left := (S1733Model_finiteEtale A).2
  have h1 : IsFinite (S1755ModelHom A) := by
    haveI : IsFinite (S1733ModelOver A).left := hfin
    exact inferInstanceAs (IsFinite ((Scheme.isoSpec (S1733Model A).left).inv ≫
      (S1733ModelOver A).left))
  have h2 : Etale (S1755ModelHom A) := by
    haveI : Etale (S1733ModelOver A).left := het
    exact inferInstanceAs (Etale ((Scheme.isoSpec (S1733Model A).left).inv ≫
      (S1733ModelOver A).left))
  exact ⟨h1, h2⟩

/-- The affine finite-etale slice object of a cover: Spec Γ(model A) together
with its finite-etale structure morphism.  No new model is chosen. -/
noncomputable def S1755SliceObject (A : S1728Cover) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (S1755ModelHom A)
    (S1755ModelHom_finiteEtale A)

@[simp] theorem S1755SliceObject_left (A : S1728Cover) :
    (S1755SliceObject A).left = S1755ModelRing A := rfl

@[simp] theorem S1755SliceObject_hom (A : S1728Cover) :
    (S1755SliceObject A).hom = S1755ModelHom A := rfl

/-! ## 4b. Auxiliary comparisons for the reverse direction -/

/-- The 2-Yoneda evaluation of a strong transformation between representable
stacks, as a function with explicit source and target. -/
noncomputable def S1755Eval (S T : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1755Y S) (S1755Y T)) : S ⟶ T :=
  S1742HomOfStrongTrans (F := S1726K) (S := S) (T := T) L

/-- The 2-Yoneda evaluation of the base-change projection is the projection. -/
theorem S1755ProjectionMap_eval (A : S1728Cover) :
    S1742HomOfStrongTrans (F := S1726K)
      (S1755BaseChange A).projectionMap.transformation = S1733ModelOver A := by
  have h := (S1755BaseChange A).projectionMap.app_eq
    (Opposite.op (S1755BaseChange A).pullbackScheme)
  simp only [S1742HomOfStrongTrans]
  rw [h]
  exact Category.id_comp _

/-- The model section lift is compatible with the projection to the base. -/
noncomputable def S1755ModelSectionProj (A : S1728Cover) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755ModelSectionLift A)
        (S1755BaseChange A).projectionMap.transformation)
      A.map :=
  (S1755BaseChange A).isPullback.liftToY (S1755Source A) (S1755IdentityCone A)

/-- Evaluation is compatible with vertical composition of strong
transformations of representable stacks. -/
theorem S1755Eval_vcomp {S T U : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans (S1755Y S) (S1755Y T))
    (L' : Pseudofunctor.StrongTrans (S1755Y T) (S1755Y U)) :
    S1755Eval S U (Pseudofunctor.StrongTrans.vcomp L L') =
      S1755Eval S T L ≫ S1755Eval T U L' := by
  have hkey := S1742Key (F := S1726K) L' (LocallyDiscrete.mk (Opposite.op S))
    (S1755Eval S T L)
  have hobj : (L.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S)) = Discrete.mk (S1755Eval S T L) :=
    Discrete.mk_as _
  simp only [S1755Eval, S1742HomOfStrongTrans]
  rw [show (Pseudofunctor.StrongTrans.vcomp L L').app
        (LocallyDiscrete.mk (Opposite.op S)) =
      L.app (LocallyDiscrete.mk (Opposite.op S)) ≫
        L'.app (LocallyDiscrete.mk (Opposite.op S)) from rfl]
  rw [Cat.Hom.comp_obj, hobj, hkey]
  rfl

/-- The strong transformation induced by a composite scheme morphism is
2-isomorphic to the composite of the induced strong transformations. -/
noncomputable def S1755StrongTransOfHomIsoComp {S T U : SchemeOverField S1726K}
    (f : S ⟶ T) (g : T ⟶ U) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) f)
        (S1742StrongTransOfHom (F := S1726K) g))
      (S1742StrongTransOfHom (F := S1726K) (f ≫ g)) :=
  S1755IsoOfEvalEq _ _ (by
    change S1755Eval S U
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1726K) f)
          (S1742StrongTransOfHom (F := S1726K) g)) =
      S1755Eval S U (S1742StrongTransOfHom (F := S1726K) (f ≫ g))
    rw [S1755Eval_vcomp,
      show S1755Eval S T (S1742StrongTransOfHom (F := S1726K) f) = f from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) f,
      show S1755Eval T U (S1742StrongTransOfHom (F := S1726K) g) = g from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) g,
      show S1755Eval S U (S1742StrongTransOfHom (F := S1726K) (f ≫ g)) = f ≫ g from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (f ≫ g)])




/-! ## 5. The exact missing statements -/

/-- The missing retraction half of stack representability of a cover by its
affine model: a strong transformation from the cover source to the model whose
composite with the base-change comparison, in the other order, is 2-isomorphic
to the identity of the model.  The opposite composite is proved
unconditionally as S1755ModelSection. -/
abbrev S1755SourceRetraction : Prop :=
  ∀ A : S1728Cover,
    ∃ inv : Pseudofunctor.StrongTrans (S1755Source A) (S1755ModelStack A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource inv)
        (Pseudofunctor.StrongTrans.id (S1755ModelStack A)))

/-- The unconditional half of representability: for every cover there is a
strong transformation from the source to the model whose composite with the
comparison is 2-isomorphic to the identity of the source. -/
theorem S1755ModelSection_exists (A : S1728Cover) :
    ∃ inv : Pseudofunctor.StrongTrans (S1755Source A) (S1755ModelStack A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp inv (S1755BaseChange A).toSource)
        (Pseudofunctor.StrongTrans.id (S1755Source A))) :=
  ⟨S1755ModelSectionLift A, ⟨S1755ModelSection A⟩⟩

/-- Full stack representability of a cover by its affine model. -/
def S1755SourceRepresentable (A : S1728Cover) : Prop :=
  ∃ inv : Pseudofunctor.StrongTrans (S1755Source A) (S1755ModelStack A),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp inv (S1755BaseChange A).toSource)
      (Pseudofunctor.StrongTrans.id (S1755Source A))) ∧
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource inv)
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A)))

/-- Full representability for all covers. -/
def S1755SourceRepresentableAll : Prop := ∀ A, S1755SourceRepresentable A

/-- Full representability implies the missing retraction half. -/
theorem S1755SourceRetraction_of_representable
    (h : S1755SourceRepresentableAll) : S1755SourceRetraction := by
  intro A
  obtain ⟨inv, -, h2⟩ := h A
  exact ⟨inv, h2⟩

/-- Under the missing retraction half of stack representability, the model
section lift itself realizes the missing retraction; the opposite composite is
the unconditional S1755ModelSection. -/
theorem S1755ModelSection_retraction (h : S1755SourceRetraction) (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource
        (S1755ModelSectionLift A))
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A))) := by
  obtain ⟨inv, ⟨einv⟩⟩ := h A
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let WA : Bicat := S1755ModelStack A
  let X : Bicat := S1755Source A
  let a : WA ⟶ X := (S1755BaseChange A).toSource
  let inv' : X ⟶ WA := inv
  let LA : X ⟶ WA := S1755ModelSectionLift A
  have eLA : LA ≫ a ≅ 𝟙 X := S1755ModelSection A
  have eInv : a ≫ inv' ≅ 𝟙 WA := einv
  have e1 : LA ≅ inv' :=
    (Bicategory.rightUnitor LA).symm ≪≫
      Bicategory.whiskerLeftIso LA eInv.symm ≪≫
        (Bicategory.associator LA a inv').symm ≪≫
          Bicategory.whiskerRightIso eLA inv' ≪≫
            Bicategory.leftUnitor inv'
  exact ⟨Bicategory.whiskerLeftIso a e1 ≪≫ eInv⟩

/-- The concrete form of the missing retraction half: the chosen base-change
comparison is a two-sided inverse of the chosen model section lift. -/
def S1755ModelRetraction : Prop :=
  ∀ A : S1728Cover,
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource
        (S1755ModelSectionLift A))
      (Pseudofunctor.StrongTrans.id (S1755ModelStack A)))

/-- The missing retraction half is exactly the concrete two-sided invertibility
of the chosen comparison against the chosen model section lift. -/
theorem S1755SourceRetraction_iff_modelRetraction :
    S1755SourceRetraction ↔ S1755ModelRetraction := by
  constructor
  · intro h
    exact S1755ModelSection_retraction h
  · intro h A
    exact ⟨S1755ModelSectionLift A, h A⟩

/-- Under the missing retraction halves, every cover source is fully
represented by its affine model, with the explicit model section lift as the
quasi-inverse. -/
theorem S1755SourceRepresentable_of_retraction
    (h : S1755SourceRetraction) : S1755SourceRepresentableAll := by
  intro A
  exact ⟨S1755ModelSectionLift A, ⟨S1755ModelSection A⟩,
    S1755ModelSection_retraction h A⟩

/-- Full stack representability of all cover sources is equivalent to the
missing retraction half. -/
theorem S1755SourceRetraction_iff_representableAll :
    S1755SourceRetraction ↔ S1755SourceRepresentableAll := by
  constructor
  · exact S1755SourceRepresentable_of_retraction
  · exact S1755SourceRetraction_of_representable

/-- The missing data of the comparison: a two-sided inverse of the extraction
on every pair of covers.  This is exactly the missing field of S1733's affine
cover model, with the S1733 model fixed. -/
structure S1755CoverModelHomEquivData (A B : S1728Cover) where
  /-- The inverse of the extraction. -/
  invFun : (S1733Model A ⟶ S1733Model B) → S1728CoverMap A B
  /-- The inverse is a left inverse of the extraction. -/
  left_inv : ∀ f : S1728CoverMap A B,
    invFun (S1755ModelHomOfCoverMap A B f) = f
  /-- The inverse is a right inverse of the extraction. -/
  right_inv : ∀ g : S1733Model A ⟶ S1733Model B,
    S1755ModelHomOfCoverMap A B (invFun g) = g

/-- The exact missing equivalence statement, with the forward map fixed to the
S1742 extraction. -/
def S1755ModelHomEquivMissing : Prop :=
  ∀ A B : S1728Cover, Nonempty (S1755CoverModelHomEquivData A B)

/-- The surjectivity half of the missing comparison: every model morphism is
the extracted image of some actual cover map. -/
def S1755ModelHomSurjective : Prop :=
  ∀ (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B),
    ∃ f : S1728CoverMap A B, S1755ModelHomOfCoverMap A B f = g

/-- The extraction packaged as an equivalence, from the missing inverse data. -/
noncomputable def S1755EquivOfData {A B : S1728Cover}
    (d : S1755CoverModelHomEquivData A B) :
    S1728CoverMap A B ≃ (S1733Model A ⟶ S1733Model B) where
  toFun := S1755ModelHomOfCoverMap A B
  invFun := d.invFun
  left_inv := d.left_inv
  right_inv := d.right_inv

/-- The missing equivalence data is exactly the bijectivity of the extraction. -/
theorem S1755ModelHomEquivMissing_iff_bijective :
    S1755ModelHomEquivMissing ↔
      ∀ A B : S1728Cover, Function.Bijective (S1755ModelHomOfCoverMap A B) := by
  constructor
  · intro h A B
    obtain ⟨d⟩ := h A B
    refine ⟨?_, ?_⟩
    · intro f g hfg
      have := d.left_inv f
      rw [hfg, d.left_inv g] at this
      exact this.symm
    · intro g
      exact ⟨d.invFun g, d.right_inv g⟩
  · intro h A B
    exact ⟨{ invFun := fun g => (Equiv.ofBijective (S1755ModelHomOfCoverMap A B) (h A B)).invFun g
             left_inv := fun f => (Equiv.ofBijective (S1755ModelHomOfCoverMap A B) (h A B)).left_inv f
             right_inv := fun g => (Equiv.ofBijective (S1755ModelHomOfCoverMap A B) (h A B)).right_inv g }⟩

/-- The missing inverse data in particular gives surjectivity of the
extraction. -/
theorem S1755ModelHomSurjective_of_modelHomEquiv
    (h : S1755ModelHomEquivMissing) : S1755ModelHomSurjective := by
  intro A B g
  obtain ⟨d⟩ := h A B
  exact ⟨d.invFun g, d.right_inv g⟩

/-! ## 6. The conditional closure of S1733's affine cover model -/

/-- The canonical affine cover model with the S1742 extraction as its hom
comparison, conditional on the missing inverse data. -/
noncomputable def S1755CanonicalAffineCoverModel
    (h : S1755ModelHomEquivMissing) : S1733AffineCoverModel where
  model := S1733Model
  toBase := S1733ModelOver
  isAffine := S1755Model_isAffine
  isFinite := fun A => (S1733Model_finiteEtale A).1
  isEtale := fun A => (S1733Model_finiteEtale A).2
  homEquiv := fun A B => (S1755EquivOfData (Classical.choice (h A B))).symm

/-- The missing inverse data inhabits S1733's first missing theorem. -/
theorem S1755AffineCoverModelMissing_of_modelHomEquiv
    (h : S1755ModelHomEquivMissing) : S1733AffineCoverModelMissing :=
  ⟨S1755CanonicalAffineCoverModel h⟩

/-- Consequently S1728's small raw cover data follow. -/
theorem S1755SmallRawCoverDataRequired_of_modelHomEquiv
    (h : S1755ModelHomEquivMissing) : S1728SmallRawCoverDataRequired :=
  S1733SmallRawCoverDataRequired_of_firstMissing
    (S1755AffineCoverModelMissing_of_modelHomEquiv h)

/-- Consequently the actual cover type carries a genuine Category.{0,1}. -/
theorem S1755Category01_of_modelHomEquiv
    (h : S1755ModelHomEquivMissing) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  S1733Category01_of_firstMissing (S1755AffineCoverModelMissing_of_modelHomEquiv h)

/-! ## 7. The slice side -/

/-- The missing slice comparison, with the object map fixed to the S1733
affine model. -/
structure S1755SliceComparison where
  /-- The comparison functor. -/
  functor : S1728Cover ⥤ S1733Slice
  /-- Its object map is the explicit affine model map. -/
  objIso : ∀ A : S1728Cover, Nonempty (functor.obj A ≅ S1755SliceObject A)
  /-- Fully faithful. -/
  fullyFaithful : functor.FullyFaithful
  /-- Essentially surjective. -/
  essSurj : functor.EssSurj

/-- The missing slice comparison, as a proposition. -/
def S1755SliceComparisonMissing : Prop := Nonempty S1755SliceComparison

/-- A fully faithful essentially surjective functor is an equivalence. -/
theorem S1755IsEquivalence_of (F : S1728Cover ⥤ S1733Slice)
    (hff : F.FullyFaithful) (h : F.EssSurj) : F.IsEquivalence :=
  ⟨hff.faithful, hff.full, h⟩

/-- The S1733 slice-equivalence target is exactly a fully faithful essentially
surjective functor to the affine finite-etale slice. -/
theorem S1755SliceFunctorMissing_iff :
    (∃ F : S1728Cover ⥤ S1733Slice, Nonempty F.FullyFaithful ∧ F.EssSurj) ↔
      S1733CoverSliceEquivalence := by
  constructor
  · rintro ⟨F, ⟨hff⟩, h⟩
    haveI : F.IsEquivalence := S1755IsEquivalence_of F hff h
    exact ⟨F.asEquivalence⟩
  · rintro ⟨e⟩
    exact ⟨e.functor, ⟨e.fullyFaithfulFunctor⟩, inferInstance⟩

/-- The comparison with the fixed object map yields S1733's slice equivalence. -/
theorem S1755CoverSliceEquivalence_of_comparison
    (d : S1755SliceComparison) : S1733CoverSliceEquivalence := by
  haveI : d.functor.IsEquivalence :=
    S1755IsEquivalence_of d.functor d.fullyFaithful d.essSurj
  exact ⟨d.functor.asEquivalence⟩

/-- The slice comparison yields essential smallness of the actual cover type. -/
theorem S1755EssentiallySmall_of_comparison
    (d : S1755SliceComparison) : EssentiallySmall.{0} S1728Cover :=
  S1733EssentiallySmall_of_sliceMissing (S1755CoverSliceEquivalence_of_comparison d)

/-- The slice comparison yields an actual Category.{0,1} on the cover type. -/
theorem S1755Category01_of_comparison
    (d : S1755SliceComparison) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  S1733Category01_of_sliceMissing (S1755CoverSliceEquivalence_of_comparison d)

/-! ## 8. Checks -/

#check S1755Y
#check S1755BaseChange
#check S1755ModelStack
#check S1755Square
#check S1755ConeCommutes
#check S1755Cone
#check S1755Lift
#check S1755Lift_toX
#check S1755Lift_toY
#check S1755ModelHomOfCoverMap
#check S1755ModelHomOfCoverMap_def
#check S1755IdentityCone
#check S1755ModelSectionLift
#check S1755ModelSection
#check S1755IsoOfEvalEq
#check S1755CoverMapRel_of_modelHom_eq
#check S1755ProjectionMap_eval
#check S1755ModelSectionProj
#check S1755Eval_vcomp
#check S1755StrongTransOfHomIsoComp
#check S1755ModelSection_retraction
#check S1755ModelRetraction
#check S1755SourceRetraction_iff_modelRetraction
#check S1755SourceRepresentable_of_retraction
#check S1755SourceRetraction_iff_representableAll
#check S1755ModelHomSurjective
#check S1755ModelHomSurjective_of_modelHomEquiv
#check S1755Model_isAffine
#check S1755SliceObject
#check S1755SourceRetraction
#check S1755ModelSection_exists
#check S1755SourceRepresentable
#check S1755SourceRetraction_of_representable
#check S1755CoverModelHomEquivData
#check S1755ModelHomEquivMissing
#check S1755EquivOfData
#check S1755ModelHomEquivMissing_iff_bijective
#check S1755CanonicalAffineCoverModel
#check S1755AffineCoverModelMissing_of_modelHomEquiv
#check S1755SmallRawCoverDataRequired_of_modelHomEquiv
#check S1755Category01_of_modelHomEquiv
#check S1755SliceComparison
#check S1755SliceComparisonMissing
#check S1755SliceFunctorMissing_iff
#check S1755CoverSliceEquivalence_of_comparison
#check S1755EssentiallySmall_of_comparison
#check S1755Category01_of_comparison

#print axioms S1755ModelHomOfCoverMap
#print axioms S1755CoverMapRel_of_modelHom_eq
#print axioms S1755ModelSection
#print axioms S1755ProjectionMap_eval
#print axioms S1755Eval_vcomp
#print axioms S1755StrongTransOfHomIsoComp
#print axioms S1755ModelSection_retraction
#print axioms S1755SourceRetraction_iff_representableAll
#print axioms S1755ModelHomEquivMissing_iff_bijective
#print axioms S1755AffineCoverModelMissing_of_modelHomEquiv
#print axioms S1755SliceFunctorMissing_iff

end LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual