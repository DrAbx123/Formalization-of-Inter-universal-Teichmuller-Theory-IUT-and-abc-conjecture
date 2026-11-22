/-
# S1733: the finite-etale cover category is not proved essentially small

## Question

Use Mathlib.AlgebraicGeometry.Morphisms.FiniteType's
essentiallySmall_costructuredArrow_Spec (the slice
P.CostructuredArrow ⊤ Scheme.Spec X) together with finite-etale
representability to prove OrbicurveFiniteEtaleCover X essentially small, or
construct Category.{0,1} on it without Shrink/ULift/PUnit.

## Findings

* The Mathlib theorem is available and is instantiated for the finite-etale
  morphism property P = IsFinite inf Etale.  It proves, for every scheme S,
  EssentiallySmall of the affine finite-etale slice over S
  (S1733AffineFiniteEtaleSlice_essentiallySmall), hence for the S1726 base
  Spec R' (S1733Slice_essentiallySmall).  Its objects are affine schemes with
  a finite-etale morphism to S; its hom types are Type 0.

* The actual cover objects are category-valued etale stacks, not affine
  schemes.  The finite-etale representability predicate gives, for every test
  scheme and point, a relative base-change presentation.  Choosing the
  identity point of the representable S1726 stack gives an affine base-change
  model S1733Model A and a finite-etale structure morphism S1733ModelOver A
  (S1733Model_finiteEtale).  The hom types between these models are Type 0,
  so the cover type carries an unconditional Category.{0,1} whose homs are
  model scheme morphisms (S1733ModelCategory).

* This model category is not the intended cover category: its homs are scheme
  morphisms between the chosen models, not the actual cover maps.  The target
  OrbicurveEtaleFundamentalGroup requires a bijection between category homs
  and OrbicurveFiniteEtaleCoverMap.  Nothing in the present definitions
  supplies:

  - an equivalence between the representable stack of the base-change model
    and the actual cover stack (the comparison map is only a 1-cell in the
    pullback square),
  - the 2-Yoneda comparison from strong transformations of representable
    stacks to scheme morphisms, or
  - the functoriality/fullness/essential surjectivity that would turn the
    models into an equivalence of categories.

* Consequently the actual cover category is not proved Small or
  EssentiallySmall.  The exact first missing geometric theorem is
  S1733AffineCoverModelMissing: an affine finite-etale model of every cover
  together with a bijection between model scheme homs and actual cover maps.
  It supports the direct Category.{0,1} branch.  For the EssentiallySmall
  branch, the exact missing theorem is S1733CoverSliceEquivalence: an
  equivalence between the S1728 2-iso cover category and the Mathlib affine
  finite-etale slice.

## What is proved unconditionally

* S1733AffineFiniteEtaleSlice_essentiallySmall / S1733Slice_essentiallySmall.
* S1733BasePoint, S1733Model, S1733ModelOver, S1733Model_finiteEtale.
* S1733ModelCategory : Category.{0,1} on the actual cover type, homs = model
  scheme morphisms.
* S1733SmallRawCoverDataOfAffineModel: the missing model supplies S1728's
  small raw cover data; the conditional actual Category.{0,1}
  S1733Category01OfAffineModel follows.
* S1733Cover_essentiallySmall_of_sliceEquiv and
  S1733Category01OfSliceEquiv: the missing slice equivalence yields
  EssentiallySmall and an actual Category.{0,1} on the cover type.

## Honest boundary

No sorry, no axiom, no Shrink, no ULift, no PUnit, and no fake category used
as the target.  The only axioms used are propext, Classical.choice, Quot.sound.
The target OrbicurveEtaleFundamentalGroup is not constructed.
S1733ModelCategory is explicitly not claimed to be the target cover category.
-/

import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.EssentiallySmall

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

universe u

/-! ## 1. The Mathlib affine finite-etale slice -/

/-- The finite-etale morphism property, as a conjunction of Mathlib's
IsFinite and Etale properties. -/
abbrev S1733FiniteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

instance : S1733FiniteEtale.{u}.RespectsIso :=
  inferInstanceAs ((@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).RespectsIso)

lemma S1733FiniteEtale_le_locallyOfFiniteType :
    S1733FiniteEtale.{u} ≤ @LocallyOfFiniteType := by
  intro X Y f hf
  haveI : IsFinite f := hf.1
  exact inferInstance

/-- Mathlib's essentially-small theorem for affine schemes locally of finite
type specializes to affine finite-etale schemes over an arbitrary base scheme.
No cover stack is involved in this statement. -/
theorem S1733AffineFiniteEtaleSlice_essentiallySmall
    (S : Scheme.{u}) :
    EssentiallySmall.{u} (S1733FiniteEtale.{u}.CostructuredArrow ⊤ Scheme.Spec S) :=
  essentiallySmall_costructuredArrow_Spec S1733FiniteEtale
    S1733FiniteEtale_le_locallyOfFiniteType

/-- The affine scheme Spec R' underlying the S1726 model. -/
noncomputable abbrev S1733BaseScheme : Scheme.{0} := S1726AffineScheme

/-- The small affine finite-etale slice over Spec R'.  Its object type is
Type 1 and its hom types are Type 0. -/
noncomputable abbrev S1733Slice : Type 1 :=
  S1733FiniteEtale.{0}.CostructuredArrow ⊤ Scheme.Spec S1733BaseScheme

example : Category.{0, 1} S1733Slice := inferInstance

/-- The affine finite-etale slice over the actual S1726 base is essentially
small. -/
theorem S1733Slice_essentiallySmall : EssentiallySmall.{0} S1733Slice :=
  S1733AffineFiniteEtaleSlice_essentiallySmall S1733BaseScheme

/-! ## 2. The base-change affine model and the model category -/

/-- The canonical identity point of the representable S1726 orbicurve stack. -/
noncomputable def S1733BasePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
      S1726Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- The affine base-change model of a finite-etale cover: pull back the cover
along the identity point of the representable base. -/
noncomputable def S1733Model (A : S1728Cover) : Iut.SchemeOverField S1726K :=
  (A.finiteEtale.baseChange S1726AffineOver S1733BasePoint).pullbackScheme

/-- The structure morphism of the model to the affine base. -/
noncomputable def S1733ModelOver (A : S1728Cover) :
    S1733Model A ⟶ S1726AffineOver :=
  (A.finiteEtale.baseChange S1726AffineOver S1733BasePoint).projection

/-- The base-change model is finite and etale over the affine base.  This is
the representability half of the finite-etale predicate, not a smallness
statement. -/
theorem S1733Model_finiteEtale (A : S1728Cover) :
    IsFinite (S1733ModelOver A).left ∧ Etale (S1733ModelOver A).left :=
  (A.finiteEtale.hasProperty S1726AffineOver S1733BasePoint)

/-- The unconditional small-hom category on the actual cover type: homs are
scheme morphisms between the base-change models.  Its object type is the actual
cover type and its hom types are Type 0, but its homs are not yet identified
with the actual cover maps, so it is not the target category. -/
@[reducible] noncomputable def S1733ModelCategory : Category.{0, 1} S1728Cover where
  Hom A B := S1733Model A ⟶ S1733Model B
  id A := 𝟙 (S1733Model A)
  comp f g := f ≫ g
  id_comp := by intro A B f; exact Category.id_comp f
  comp_id := by intro A B f; exact Category.comp_id f
  assoc := by intro A B C D f g h; exact Category.assoc f g h

/-! ## 3. The exact missing affine cover model -/

/-- A chosen affine finite-etale model of every actual cover, together with a
bijection between model scheme morphisms and actual raw cover maps.  This is
the precise geometric input that the relative finite-etale representability
predicate does not supply.

It would give, through S1728's conditional construction, an actual
Category.{0,1} on the cover type.  It does not by itself give object-level
essential smallness; that is the separate slice-equivalence target below. -/
structure S1733AffineCoverModel where
  model : S1728Cover → Iut.SchemeOverField S1726K
  toBase : ∀ A, model A ⟶ S1726AffineOver
  isAffine : ∀ A, IsAffine (model A).left
  isFinite : ∀ A, IsFinite (toBase A).left
  isEtale : ∀ A, Etale (toBase A).left
  homEquiv : ∀ A B, (model A ⟶ model B) ≃ S1728CoverMap A B

/-- The exact first missing geometric theorem for the direct small-category
route. -/
def S1733AffineCoverModelMissing : Prop := Nonempty S1733AffineCoverModel

/-- The model supplies small raw cover data in the sense of S1728. -/
theorem S1733SmallRawCoverDataOfAffineModel
    (M : S1733AffineCoverModel) (A B : S1728Cover) :
    Nonempty (S1728ActualSmallRawCoverData A B) :=
  ⟨{ Carrier := M.model A ⟶ M.model B
     equiv := M.homEquiv A B }⟩

/-- The conditional actual Category.{0,1} on the cover type from the missing
affine model.  No Shrink, ULift or PUnit is used. -/
@[reducible] noncomputable def S1733Category01OfAffineModel
    (M : S1733AffineCoverModel) : Category.{0, 1} S1728Cover :=
  S1728ActualCategory01
    (fun A B => M.model A ⟶ M.model B)
    M.homEquiv

/-! ## 4. The slice-equivalence route to essential smallness -/

/-- The exact categorical comparison whose absence blocks transporting
Mathlib's EssentiallySmall of the affine finite-etale slice to the actual
cover category.  It is the 2-categorical representation theorem: every actual
finite-etale cover is represented by an affine finite-etale scheme over the
base, and every 2-iso class of cover maps is a scheme map between such models. -/
def S1733CoverSliceEquivalence : Prop :=
  Nonempty (@CategoryTheory.Equivalence S1728Cover S1733Slice
    S1728ActualCategory11 inferInstance)

/-- Conditional actual Category.{0,1} on the cover type from the missing slice
equivalence.  Homs are the Type 0 homs of the small slice, transported along
the object map of the equivalence; no Shrink/ULift/PUnit is used.  This
category has model homs; identifying them with the actual cover maps is the
next missing step (S1733AffineCoverModel). -/
@[reducible] noncomputable def S1733Category01OfSliceEquiv
    (e : @CategoryTheory.Equivalence S1728Cover S1733Slice
      S1728ActualCategory11 inferInstance) :
    Category.{0, 1} S1728Cover where
  Hom A B := e.functor.obj A ⟶ e.functor.obj B
  id A := 𝟙 (e.functor.obj A)
  comp f g := f ≫ g
  id_comp := by intro A B f; exact Category.id_comp f
  comp_id := by intro A B f; exact Category.comp_id f
  assoc := by intro A B C D f g h; exact Category.assoc f g h

/-- Conditional EssentiallySmall of the actual S1728 cover category from the
missing slice equivalence. -/
theorem S1733Cover_essentiallySmall_of_sliceEquiv
    (e : @CategoryTheory.Equivalence S1728Cover S1733Slice
      S1728ActualCategory11 inferInstance) :
    EssentiallySmall.{0} S1728Cover := by
  rcases S1733Slice_essentiallySmall with ⟨D, hD, ⟨eD⟩⟩
  exact ⟨D, hD, ⟨e.trans eD⟩⟩

/-! ## 5. Closure statements for the exact missing theorems -/

/-- The missing affine cover model supplies exactly S1728's small raw cover
data requirement. -/
theorem S1733SmallRawCoverDataRequired_of_firstMissing
    (h : S1733AffineCoverModelMissing) : S1728SmallRawCoverDataRequired := by
  rcases h with ⟨M⟩
  intro A B
  exact S1733SmallRawCoverDataOfAffineModel M A B

/-- The missing affine cover model gives an actual Category.{0,1} on the
actual cover type. -/
theorem S1733Category01_of_firstMissing
    (h : S1733AffineCoverModelMissing) :
    Nonempty (Category.{0, 1} S1728Cover) := by
  rcases h with ⟨M⟩
  exact ⟨S1733Category01OfAffineModel M⟩

/-- The missing slice comparison gives EssentiallySmall of the actual S1728
cover category. -/
theorem S1733EssentiallySmall_of_sliceMissing
    (h : S1733CoverSliceEquivalence) : EssentiallySmall.{0} S1728Cover := by
  rcases h with ⟨e⟩
  exact S1733Cover_essentiallySmall_of_sliceEquiv e

/-- The missing slice comparison gives an actual Category.{0,1} on the actual
cover type (with model hom types). -/
theorem S1733Category01_of_sliceMissing
    (h : S1733CoverSliceEquivalence) :
    Nonempty (Category.{0, 1} S1728Cover) := by
  rcases h with ⟨e⟩
  exact ⟨S1733Category01OfSliceEquiv e⟩

/-! ## 6. Checks -/

#check S1733FiniteEtale
#check S1733AffineFiniteEtaleSlice_essentiallySmall
#check S1733Slice
#check S1733Slice_essentiallySmall
#check S1733BasePoint
#check S1733Model
#check S1733ModelOver
#check S1733Model_finiteEtale
#check S1733ModelCategory
#check S1733AffineCoverModel
#check S1733AffineCoverModelMissing
#check S1733SmallRawCoverDataOfAffineModel
#check S1733Category01OfAffineModel
#check S1733CoverSliceEquivalence
#check S1733Category01OfSliceEquiv
#check S1733Cover_essentiallySmall_of_sliceEquiv
#check S1733SmallRawCoverDataRequired_of_firstMissing
#check S1733Category01_of_firstMissing
#check S1733EssentiallySmall_of_sliceMissing
#check S1733Category01_of_sliceMissing

#print axioms S1733AffineFiniteEtaleSlice_essentiallySmall
#print axioms S1733Slice_essentiallySmall
#print axioms S1733Model_finiteEtale
#print axioms S1733SmallRawCoverDataOfAffineModel
#print axioms S1733Cover_essentiallySmall_of_sliceEquiv
#print axioms S1733SmallRawCoverDataRequired_of_firstMissing
#print axioms S1733Category01_of_firstMissing
#print axioms S1733EssentiallySmall_of_sliceMissing
#print axioms S1733Category01_of_sliceMissing

end LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
