/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1743CoverSliceActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual

/-!
# S1744: assembling an actual Category.{0,1} from the S1733 missing statements

## Question

S1733 reduced the categorical field of the target
OrbicurveEtaleFundamentalGroup to two missing statements:

* S1733AffineCoverModel: an affine finite etale model of every actual cover
  together with a bijection between model scheme morphisms and the actual raw
  cover maps;
* S1733CoverSliceEquivalence: an equivalence between the actual
  2-isomorphism-quotient cover category and Mathlib's affine finite etale slice
  over Spec R'.

This file attempts to construct an inhabitant of either, and otherwise reduces
them to smaller, precisely stated lemmas.

## Result

No inhabitant of either missing statement is constructed, and the file explains
exactly why.  The following *is* now constructed or proved unconditionally.

1. The canonical base-change model of S1733 carries **all geometric fields** of
   S1733AffineCoverModel.  S1733 proved IsFinite and Etale of the model
   projection; the genuinely new field is IsAffine, which follows because a
   finite morphism is affine and the target Spec R' is affine
   (isAffine_of_isAffineHom).  Hence S1744ModelData has an unconditional
   inhabitant S1744CanonicalModelData.

2. S1733AffineCoverModel is *exactly* "model data + the hom comparison"
   (S1744AffineCoverModelMissing_iff).  Five of its six fields are therefore
   discharged; the whole missing content is the field

     homEquiv : forall A B, (model A --> model B) equiv S1728CoverMap A B.

3. On the slice side the object-level comparison is unconditional: every cover
   has an affine finite etale model over the base, and the global sections of
   that model with Scheme.isoSpec give an actual object S1744SliceObject A of
   Mathlib's affine finite etale slice.  The slice itself is unconditionally
   nonempty (S1744SliceIdentityObject).

4. **The action of cover maps on the canonical models is constructed**
   (S1744ModelMapOfCoverMap): compose the chosen base-change presentation of A
   with the cover map and with S1743's unconditional lift of B, obtaining a
   strong transformation Y(model A) -> Y(model B), and apply S1742's 2-Yoneda
   realisation to get an actual morphism S1733Model A -> S1733Model B over the
   base.  Hence S1744RepresentableModelFunctoriality holds unconditionally
   (S1744RepresentableModelFunctoriality_holds).  This uses only the parallel
   results S1742 (2-Yoneda) and S1743 (the identity-point lift).

## The exact residual lemma list

Direct route (S1733AffineCoverModel, hence S1728SmallRawCoverDataRequired and
Nonempty (Category.{0,1})):

* R1.  S1744ModelHomAction: a function family
  forall A B, S1728CoverMap A B -> (S1733Model A --> S1733Model B), i.e. the
  chosen base-change presentations are functorial in the cover map.
  **Discharged.**  R1a (2-Yoneda for representable etale pseudofunctors) is
  S1742; R1b (the action itself) is S1744ModelMapOfCoverMap, built from S1742's
  realisation plus S1743's lift, and S1744RepresentableModelFunctoriality_holds
  records it.
* R2.  S1744ModelHomActionBijective: the remaining comparison.  Injectivity is
  the faithfulness part of 2-Yoneda.  Surjectivity is a genuinely geometric
  statement that a morphism of the models at one test scheme (the identity point
  of the base) extends to a map of the etale stacks.  Nothing in the definitions
  supplies it: EtaleStackRepresentableMorphismProperty.baseChange chooses one
  presentation of every cover at every test scheme and point, with no
  compatibility in the stack morphism, so the presentations of two different
  covers are unrelated; finite etale descent is not available in the tree.
  Moreover injectivity of *this* action is doubtful for a structural reason:
  the construction only evaluates at the identity point (through the lift of
  S1743), so two cover maps that differ away from that point can a priori have
  the same model morphism; the S1733AffineCoverModel homEquiv therefore is not
  forced by the present data for the canonical model choice.
  S1744ModelHomComparison packages the action + R2 + the two inverse laws, and
  S1744CanonicalModelHomEquiv is the equivalent equivalence form.

Slice route (S1733CoverSliceEquivalence):

* S1.  S1744SliceFunctorSpec: a functor S1728Cover --> S1733Slice which is
  faithful, full and essentially surjective.  This is *equivalent* to
  S1733CoverSliceEquivalence (S1744CoverSliceEquivalence_iff); the object part
  is available (S1744SliceObject), the missing part is again the action on
  morphisms (R1-type 2-Yoneda) plus the three comparison properties.

No vacuous shortcut: S1733CoverSliceEquivalence constructs an actual cover
(S1744Cover_nonempty_of_sliceEquivalence), since the slice is nonempty and an
equivalence is essentially surjective.  So the slice route cannot be discharged
by proving the cover type empty, and the two missing statements are not
inter-derivable in the present state: the affine-cover route needs an
equivalence on *raw* cover maps (Type 1), while the slice route only compares
2-isomorphism classes.

## Recommended next step

The direct route is now exactly R2: bijectivity of the constructed action
(S1744CanonicalModelHomBijective).  Recommended split:

* R2a (injectivity).  Expect it to *fail* for the canonical base-change model:
  the action only sees the identity point.  A useful next theorem is therefore
  the negative one -- the action is constant on cover maps that are related by
  a 2-cell over the identity point -- and then a corrected model choice (e.g.
  all test points, or a presentation that records the map on homs).
* R2b (surjectivity).  This is finite etale descent: an over-morphism of the
  identity-point models extends to a strong transformation of the etale
  stacks.  It is the one place where new geometry (or the connected-cover
  classification of S1728SmallGaloisModel) is genuinely required.
* Slice route S1: build the functor on morphisms from the same ingredients
  (S1742 realisation applied to Y(model A) -> A.source -> B.source ->
  Y(model B), as in S1744ModelMapOfCoverMap) and then prove full, faithful and
  essentially surjective.  The object part is S1744SliceObject.

## Honest boundary

No sorry, no axiom, no Shrink, ULift or PUnit, and no fake category.  The target
OrbicurveEtaleFundamentalGroup, S1733Category01, S1728SmallRawCoverDataRequired
and the two S1733 missing statements are not inhabited here.  Only propext,
Classical.choice and Quot.sound are used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 0. The category structure used by the slice comparison

This is S1733's S1728ActualCategory11, declared as a local instance only so
that the statements below can be written with the ordinary functor notation.
It is not a new category and it is not an instance for Category.{0,1}. -/

local instance S1744CoverCategory : Category.{1, 1} S1728Cover := S1728ActualCategory11

/-! ## 1. Affineness of the canonical base-change models -/

/-- The affine base Spec R' is affine. -/
theorem S1744Base_isAffine : IsAffine (Over.left S1726AffineOver) := by
  change IsAffine (Spec (CommRingCat.of S1726CoordinateRing))
  exact isAffine_Spec _

/-- S1733's base-change model of every cover is affine: its projection is
finite (S1733Model_finiteEtale), hence an affine morphism, and the target
Spec R' is affine. -/
theorem S1744Model_isAffine (A : S1728Cover) :
    IsAffine (Over.left (S1733Model A)) := by
  haveI hfin : IsFinite (Over.Hom.left (S1733ModelOver A)) :=
    (S1733Model_finiteEtale A).1
  haveI : IsAffineHom (Over.Hom.left (S1733ModelOver A)) := inferInstance
  haveI : IsAffine (Over.left S1726AffineOver) := S1744Base_isAffine
  exact isAffine_of_isAffineHom (f := Over.Hom.left (S1733ModelOver A))

attribute [local instance] S1744Model_isAffine

/-! ## 2. Model data: the geometric part of S1733's first missing statement -/

/-- All geometric fields of S1733AffineCoverModel, without the hom comparison.
Every field is an honest affine-geometry statement about actual schemes; none
of them mentions the raw cover maps. -/
structure S1744ModelData where
  model : S1728Cover → Iut.SchemeOverField S1726K
  toBase : ∀ A, model A ⟶ S1726AffineOver
  isAffine : ∀ A, IsAffine (model A).left
  isFinite : ∀ A, IsFinite (toBase A).left
  isEtale : ∀ A, Etale (toBase A).left

/-- The unconditional inhabitant: S1733's base-change model. -/
def S1744CanonicalModelData : S1744ModelData where
  model := S1733Model
  toBase := S1733ModelOver
  isAffine := S1744Model_isAffine
  isFinite := fun A => (S1733Model_finiteEtale A).1
  isEtale := fun A => (S1733Model_finiteEtale A).2

/-- Model data is not the obstruction: it exists unconditionally. -/
theorem S1744ModelData_nonempty : Nonempty S1744ModelData :=
  ⟨S1744CanonicalModelData⟩

/-- Project the geometric data out of any S1733 affine cover model. -/
def S1744ModelDataOfAffineCoverModel (M : S1733AffineCoverModel) :
    S1744ModelData where
  model := M.model
  toBase := M.toBase
  isAffine := M.isAffine
  isFinite := M.isFinite
  isEtale := M.isEtale

/-- Model data together with the hom comparison is exactly S1733's affine cover
model. -/
def S1744AffineCoverModelOf (M : S1744ModelData)
    (e : ∀ A B, (M.model A ⟶ M.model B) ≃ S1728CoverMap A B) :
    S1733AffineCoverModel where
  model := M.model
  toBase := M.toBase
  isAffine := M.isAffine
  isFinite := M.isFinite
  isEtale := M.isEtale
  homEquiv := e

theorem S1744AffineCoverModelMissing_of (M : S1744ModelData)
    (e : ∀ A B, (M.model A ⟶ M.model B) ≃ S1728CoverMap A B) :
    S1733AffineCoverModelMissing :=
  ⟨S1744AffineCoverModelOf M e⟩

/-- **Exact reduction of S1733's first missing statement**: it is precisely the
existence of model data together with the hom comparison.  The geometric data is
supplied by S1744CanonicalModelData; the only missing input is the equivalence
of hom types. -/
theorem S1744AffineCoverModelMissing_iff :
    S1733AffineCoverModelMissing ↔
      ∃ M : S1744ModelData,
        Nonempty (∀ A B, (M.model A ⟶ M.model B) ≃ S1728CoverMap A B) := by
  constructor
  · rintro ⟨M⟩
    exact ⟨S1744ModelDataOfAffineCoverModel M, ⟨M.homEquiv⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact S1744AffineCoverModelMissing_of M e

/-! ## 3. The hom comparison, split into smaller lemmas -/

/-- The two directions of the model/cover-map comparison together with their two
inverse laws.  This is the exact content of the missing homEquiv field, with the
two geometric directions separated. -/
structure S1744ModelHomComparison (M : S1744ModelData) where
  homToModel : ∀ A B, S1728CoverMap A B → (M.model A ⟶ M.model B)
  homToCover : ∀ A B, (M.model A ⟶ M.model B) → S1728CoverMap A B
  homToCover_homToModel :
    ∀ (A B : S1728Cover) (f : S1728CoverMap A B),
      homToCover A B (homToModel A B f) = f
  homToModel_homToCover :
    ∀ (A B : S1728Cover) (g : M.model A ⟶ M.model B),
      homToModel A B (homToCover A B g) = g

/-- The comparison structure is exactly the hom-equivalence family. -/
theorem S1744ModelHomComparison_iff (M : S1744ModelData) :
    Nonempty (S1744ModelHomComparison M) ↔
      Nonempty (∀ A B, (M.model A ⟶ M.model B) ≃ S1728CoverMap A B) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨fun A B =>
      { toFun := C.homToCover A B
        invFun := C.homToModel A B
        left_inv := C.homToModel_homToCover A B
        right_inv := C.homToCover_homToModel A B }⟩
  · rintro ⟨e⟩
    exact ⟨{ homToModel := fun A B f => (e A B).invFun f
             homToCover := fun A B g => (e A B).toFun g
             homToCover_homToModel := fun A B f => (e A B).right_inv f
             homToModel_homToCover := fun A B g => (e A B).left_inv g }⟩

/-- The geometrically constructible direction: cover maps act on the chosen
models through the chosen base-change presentations.  Constructing it is next
step R1 (2-Yoneda plus presentation coherence). -/
def S1744ModelHomAction (M : S1744ModelData) : Type 1 :=
  ∀ A B : S1728Cover, S1728CoverMap A B → (M.model A ⟶ M.model B)

/-- The remaining comparison statement: the action is bijective.  Injectivity is
the faithfulness half of 2-Yoneda; surjectivity is the geometric
extension/descent statement. -/
def S1744ModelHomActionBijective (M : S1744ModelData)
    (act : S1744ModelHomAction M) : Prop :=
  ∀ A B, Function.Bijective (act A B)

/-- The comparison structure is exactly an action together with bijectivity. -/
theorem S1744ModelHomComparison_iff_action (M : S1744ModelData) :
    Nonempty (S1744ModelHomComparison M) ↔
      ∃ act : S1744ModelHomAction M, S1744ModelHomActionBijective M act := by
  constructor
  · rintro ⟨C⟩
    refine ⟨C.homToModel, fun A B => ?_⟩
    refine ⟨fun f g h => ?_,
      fun g => ⟨C.homToCover A B g, C.homToModel_homToCover A B g⟩⟩
    simpa only [C.homToCover_homToModel A B f, C.homToCover_homToModel A B g] using
      congrArg (fun x => C.homToCover A B x) h
  · rintro ⟨act, hbij⟩
    exact ⟨{ homToModel := act
             homToCover := fun A B g => Classical.choose ((hbij A B).2 g)
             homToCover_homToModel := fun A B f =>
               (hbij A B).1 (Classical.choose_spec ((hbij A B).2 (act A B f)))
             homToModel_homToCover := fun A B g =>
               Classical.choose_spec ((hbij A B).2 g) }⟩

/-! ## 4. The single missing input of the direct route and its consequences -/

/-- The canonical form of the only missing input: the canonical model's hom types
are equivalent to the actual raw cover-map types. -/
def S1744CanonicalModelHomEquiv : Prop :=
  Nonempty (∀ A B, (S1733Model A ⟶ S1733Model B) ≃ S1728CoverMap A B)

theorem S1744CanonicalModelHomEquiv_iff_comparison :
    S1744CanonicalModelHomEquiv ↔
      Nonempty (S1744ModelHomComparison S1744CanonicalModelData) := by
  have h := S1744ModelHomComparison_iff S1744CanonicalModelData
  simpa only [S1744CanonicalModelHomEquiv, S1744CanonicalModelData] using h.symm

/-- The canonical action: cover maps act on the canonical models. -/
def S1744CanonicalModelHomAction : Type 1 :=
  S1744ModelHomAction S1744CanonicalModelData

/-- Bijectivity of the canonical action. -/
def S1744CanonicalModelHomActionBijective
    (act : S1744CanonicalModelHomAction) : Prop :=
  S1744ModelHomActionBijective S1744CanonicalModelData act

/-- The canonical missing input, split into S1744ModelHomAction and
S1744ModelHomActionBijective. -/
theorem S1744CanonicalModelHomEquiv_iff_action :
    S1744CanonicalModelHomEquiv ↔
      ∃ act : S1744CanonicalModelHomAction,
        S1744CanonicalModelHomActionBijective act :=
  S1744CanonicalModelHomEquiv_iff_comparison.trans
    (S1744ModelHomComparison_iff_action S1744CanonicalModelData)

/-- **The action type, named for the direct route**: cover maps act on the
canonical models. -/
def S1744RepresentableModelFunctoriality : Prop :=
  Nonempty S1744CanonicalModelHomAction

/-- **R2 (injectivity)**: injectivity of the canonical action is the faithfulness
half of 2-Yoneda. -/
def S1744CanonicalModelHomActionInjective
    (act : S1744CanonicalModelHomAction) : Prop :=
  ∀ A B, Function.Injective (act A B)

/-- **R2 (surjectivity)**: surjectivity is the geometric extension/descent
statement that a morphism between the models at the identity point of the base
extends to a map of the etale stacks. -/
def S1744CanonicalModelHomActionSurjective
    (act : S1744CanonicalModelHomAction) : Prop :=
  ∀ A B, Function.Surjective (act A B)

/-- Bijectivity is injectivity together with surjectivity. -/
theorem S1744CanonicalModelHomActionBijective_iff
    (act : S1744CanonicalModelHomAction) :
    S1744CanonicalModelHomActionBijective act ↔
      S1744CanonicalModelHomActionInjective act ∧
        S1744CanonicalModelHomActionSurjective act :=
  ⟨fun h => ⟨fun A B => (h A B).1, fun A B => (h A B).2⟩,
   fun h A B => ⟨h.1 A B, h.2 A B⟩⟩

/-- **R2**: the remaining comparison is the bijectivity of the canonical
action. -/
def S1744CanonicalModelHomBijective : Prop :=
  ∃ act : S1744CanonicalModelHomAction,
    S1744CanonicalModelHomActionBijective act

/-- S1733's first missing statement follows from the single canonical hom
equivalence. -/
theorem S1744AffineCoverModelMissing_of_canonicalHomEquiv
    (h : S1744CanonicalModelHomEquiv) : S1733AffineCoverModelMissing := by
  rcases h with ⟨e⟩
  exact S1744AffineCoverModelMissing_of S1744CanonicalModelData e

/-- The same input supplies S1728's small raw cover data. -/
theorem S1744SmallRawCoverDataRequired_of_canonicalHomEquiv
    (h : S1744CanonicalModelHomEquiv) : S1728SmallRawCoverDataRequired :=
  S1733SmallRawCoverDataRequired_of_firstMissing
    (S1744AffineCoverModelMissing_of_canonicalHomEquiv h)

/-- The same input supplies an actual Category.{0,1} on the cover type. -/
theorem S1744Category01_of_canonicalHomEquiv
    (h : S1744CanonicalModelHomEquiv) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  S1733Category01_of_firstMissing
    (S1744AffineCoverModelMissing_of_canonicalHomEquiv h)

/-- General form: model data plus the hom equivalence gives the small raw cover
data. -/
theorem S1744SmallRawCoverDataRequired_of_modelData (M : S1744ModelData)
    (e : ∀ A B, (M.model A ⟶ M.model B) ≃ S1728CoverMap A B) :
    S1728SmallRawCoverDataRequired :=
  S1733SmallRawCoverDataRequired_of_firstMissing
    (S1744AffineCoverModelMissing_of M e)

/-! ## 4b. The action of cover maps on the canonical models (constructed) -/

/-- The representable etale pseudofunctor of a scheme over the base. -/
noncomputable abbrev S1744Y (S : Iut.SchemeOverField S1726K) :
    Iut.EtaleStackPseudofunctor S1726K :=
  Iut.schemeRepresentableEtalePseudofunctor S1726K S

/-- The identity-point base-change presentation of a cover: the presentation
used by S1733's model.  It is part of the finite-etale predicate, not an extra
choice. -/
noncomputable def S1744BaseChange (A : S1728Cover) :
    Iut.EtaleStackBaseChangePresentation A.map S1726AffineOver S1733BasePoint :=
  A.finiteEtale.baseChange S1726AffineOver S1733BasePoint

/-- **The action of a cover map on the canonical models.**  A cover map
f : A.source ⟶ B.source is composed with the chosen base-change presentation of
A (a strong transformation Y (model A) ⟶ A.source) and with S1743's
unconditional lift B.source ⟶ Y (model B); this gives a strong transformation
Y (model A) ⟶ Y (model B), and S1742's 2-Yoneda realisation turns it into an
actual morphism S1733Model A ⟶ S1733Model B over the base.

Both inputs are unconditional: the presentation belongs to the finite-etale
predicate and the lift is S1743's S1743Lift.  Hence the "functoriality"
direction of the missing hom comparison is *constructed*, not assumed. -/
noncomputable def S1744ModelMapOfCoverMap (A B : S1728Cover)
    (f : S1728CoverMap A B) : S1733Model A ⟶ S1733Model B :=
  S1742HomOfStrongTrans (F := S1726K) (S := S1733Model A) (T := S1733Model B)
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (S1744BaseChange A).toSource f.map)
      (S1743Lift B))

/-- The canonical action as an actual inhabitant of the action type. -/
noncomputable def S1744CanonicalModelHomActionActual :
    S1744CanonicalModelHomAction :=
  fun A B f => S1744ModelMapOfCoverMap A B f

/-- **R1b is unconditional**: cover maps act on the canonical models. -/
theorem S1744RepresentableModelFunctoriality_holds :
    S1744RepresentableModelFunctoriality :=
  ⟨S1744CanonicalModelHomActionActual⟩

/-- The residual for the direct route is exactly the bijectivity of the
constructed action. -/
theorem S1744SmallRawCoverDataRequired_of_bijective
    (hR2 : S1744CanonicalModelHomBijective) :
    S1728SmallRawCoverDataRequired := by
  have h : S1744CanonicalModelHomEquiv :=
    S1744CanonicalModelHomEquiv_iff_action.mpr hR2
  exact S1744SmallRawCoverDataRequired_of_canonicalHomEquiv h

/-- Alias keeping the residual-list name used in the summary. -/
theorem S1744SmallRawCoverDataRequired_of_residual
    (hR2 : S1744CanonicalModelHomBijective) :
    S1728SmallRawCoverDataRequired :=
  S1744SmallRawCoverDataRequired_of_bijective hR2

/-! ## 5. The slice side: the object-level comparison is available -/

/-- The identity object of Mathlib's affine finite etale slice over Spec R':
Spec R' over itself.  It shows unconditionally that the slice is nonempty. -/
noncomputable def S1744SliceIdentityObject : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤)
    (A := Opposite.op (CommRingCat.of S1726CoordinateRing))
    (𝟙 (Spec (CommRingCat.of S1726CoordinateRing)))
    (by
      have hfin : IsFinite (𝟙 (Spec (CommRingCat.of S1726CoordinateRing))) :=
        inferInstance
      have het : Etale (𝟙 (Spec (CommRingCat.of S1726CoordinateRing))) :=
        inferInstance
      change IsFinite (𝟙 (Spec (CommRingCat.of S1726CoordinateRing))) ∧
        Etale (𝟙 (Spec (CommRingCat.of S1726CoordinateRing)))
      exact ⟨hfin, het⟩)

/-- The slice is nonempty unconditionally. -/
theorem S1744Slice_nonempty : Nonempty S1733Slice :=
  ⟨S1744SliceIdentityObject⟩

/-- **The object-level shadow of the slice comparison**: every actual cover has an
affine finite etale model over the base; taking global sections of that affine
model (Scheme.isoSpec) gives an actual object of Mathlib's affine finite etale
slice.  This is the part of S1733CoverSliceEquivalence that is available without
further geometric input. -/
noncomputable def S1744SliceObject (A : S1728Cover) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤)
    (A := Opposite.op
      (Γ(Over.left (S1733Model A), (⊤ : (Over.left (S1733Model A)).Opens))))
    ((Scheme.isoSpec (Over.left (S1733Model A))).inv ≫
      Over.Hom.left (S1733ModelOver A))
    (by
      haveI hfin : IsFinite (Over.Hom.left (S1733ModelOver A)) :=
        (S1733Model_finiteEtale A).1
      haveI het : Etale (Over.Hom.left (S1733ModelOver A)) :=
        (S1733Model_finiteEtale A).2
      have hcomp_fin :
          IsFinite ((Scheme.isoSpec (Over.left (S1733Model A))).inv ≫
            Over.Hom.left (S1733ModelOver A)) := inferInstanceAs (IsFinite _)
      have hcomp_et :
          Etale ((Scheme.isoSpec (Over.left (S1733Model A))).inv ≫
            Over.Hom.left (S1733ModelOver A)) := inferInstanceAs (Etale _)
      change IsFinite ((Scheme.isoSpec (Over.left (S1733Model A))).inv ≫
          Over.Hom.left (S1733ModelOver A)) ∧
        Etale ((Scheme.isoSpec (Over.left (S1733Model A))).inv ≫
          Over.Hom.left (S1733ModelOver A))
      exact ⟨hcomp_fin, hcomp_et⟩)

/-- The slice object carries a finite etale structure morphism. -/
theorem S1744SliceObject_prop (A : S1728Cover) :
    S1733FiniteEtale (S1744SliceObject A).hom :=
  (S1744SliceObject A).prop

/-- The slice comparison, split into a functor plus its three comparison
properties.  The object part is S1744SliceObject; the action on morphisms and
the three properties are the missing content. -/
def S1744SliceFunctorSpec : Prop :=
  ∃ F : S1728Cover ⥤ S1733Slice,
    Functor.Faithful F ∧ Functor.Full F ∧ Functor.EssSurj F

/-- **Exact reduction of S1733's second missing statement**: the slice
equivalence is precisely a faithful, full and essentially surjective functor into
the affine finite etale slice. -/
theorem S1744CoverSliceEquivalence_iff :
    S1733CoverSliceEquivalence ↔ S1744SliceFunctorSpec := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.functor, inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨F, hf, hfull, hE⟩
    haveI : Functor.IsEquivalence F := ⟨hf, hfull, hE⟩
    exact ⟨F.asEquivalence⟩

/-- The slice route constructs an actual cover.  Hence it cannot be discharged by
proving that the cover type is empty. -/
theorem S1744Cover_nonempty_of_sliceEquivalence
    (h : S1733CoverSliceEquivalence) : Nonempty S1728Cover := by
  rcases h with ⟨e⟩
  haveI : e.functor.EssSurj := inferInstance
  exact ⟨e.functor.objPreimage S1744SliceIdentityObject⟩

/-- The slice route gives essential smallness of the actual cover category
(restating S1733's conditional theorem through the split form). -/
theorem S1744EssentiallySmall_of_sliceEquivalence
    (h : S1733CoverSliceEquivalence) : EssentiallySmall.{0} S1728Cover :=
  S1733EssentiallySmall_of_sliceMissing h

/-! ## 6. The named next steps -/

/-- **Step R1a, discharged by S1742.**  The bicategorical 2-Yoneda comparison
for the representable etale pseudofunctor: S1742 constructs
S1742HomOfStrongTrans : StrongTrans (Y S) (Y T) → (S ⟶ T) and proves that it is
inverse to S1742StrongTransOfHom (strictly in one direction and up to
2-isomorphism in the other).  This file uses it in
S1744ModelMapOfCoverMap.  The proposition below records the comparison in the
weaker "bijection up to 2-isomorphism" form; it is not needed for the
construction above. -/
def S1744RepresentableStrongTransEquiv : Prop :=
  ∀ S T : Iut.SchemeOverField S1726K,
    Nonempty
      (Pseudofunctor.StrongTrans
          (Iut.schemeRepresentableEtalePseudofunctor S1726K S)
          (Iut.schemeRepresentableEtalePseudofunctor S1726K T) ≃ (S ⟶ T))

/-! ## 7. Checks -/

#check S1744Base_isAffine
#check S1744Model_isAffine
#check S1744ModelData
#check S1744CanonicalModelData
#check S1744ModelData_nonempty
#check S1744ModelDataOfAffineCoverModel
#check S1744AffineCoverModelOf
#check S1744AffineCoverModelMissing_iff
#check S1744ModelHomComparison
#check S1744ModelHomComparison_iff
#check S1744ModelHomAction
#check S1744ModelHomActionBijective
#check S1744ModelHomComparison_iff_action
#check S1744CanonicalModelHomEquiv
#check S1744CanonicalModelHomEquiv_iff_comparison
#check S1744CanonicalModelHomEquiv_iff_action
#check S1744AffineCoverModelMissing_of_canonicalHomEquiv
#check S1744SmallRawCoverDataRequired_of_canonicalHomEquiv
#check S1744Category01_of_canonicalHomEquiv
#check S1744SliceIdentityObject
#check S1744Slice_nonempty
#check S1744SliceObject
#check S1744SliceObject_prop
#check S1744SliceFunctorSpec
#check S1744CoverSliceEquivalence_iff
#check S1744Cover_nonempty_of_sliceEquivalence
#check S1744EssentiallySmall_of_sliceEquivalence
#check S1744Y
#check S1744BaseChange
#check S1744ModelMapOfCoverMap
#check S1744CanonicalModelHomActionActual
#check S1744RepresentableStrongTransEquiv
#check S1744RepresentableModelFunctoriality
#check S1744RepresentableModelFunctoriality_holds
#check S1744CanonicalModelHomBijective
#check S1744SmallRawCoverDataRequired_of_bijective
#check S1744SmallRawCoverDataRequired_of_residual

#print axioms S1744Base_isAffine
#print axioms S1744Model_isAffine
#print axioms S1744CanonicalModelData
#print axioms S1744ModelData_nonempty
#print axioms S1744AffineCoverModelMissing_iff
#print axioms S1744ModelHomComparison_iff
#print axioms S1744ModelHomComparison_iff_action
#print axioms S1744CanonicalModelHomEquiv_iff_comparison
#print axioms S1744CanonicalModelHomEquiv_iff_action
#print axioms S1744AffineCoverModelMissing_of_canonicalHomEquiv
#print axioms S1744SmallRawCoverDataRequired_of_canonicalHomEquiv
#print axioms S1744Category01_of_canonicalHomEquiv
#print axioms S1744SliceIdentityObject
#print axioms S1744SliceObject
#print axioms S1744CoverSliceEquivalence_iff
#print axioms S1744Cover_nonempty_of_sliceEquivalence
#print axioms S1744EssentiallySmall_of_sliceEquivalence
#print axioms S1744ModelMapOfCoverMap
#print axioms S1744CanonicalModelHomActionActual
#print axioms S1744RepresentableModelFunctoriality_holds
#print axioms S1744SmallRawCoverDataRequired_of_bijective
#print axioms S1744SmallRawCoverDataRequired_of_residual

end LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
