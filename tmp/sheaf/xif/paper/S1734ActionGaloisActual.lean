/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Galois.Examples

/-!
# S1734: Mathlib's small Galois category for the absolute Galois group of F'

This file performs the small-category step toward the finite-étale Galois
category of the S1726 orbicurve.  It uses Mathlib's small Galois category of
finite G-sets as the candidate small model.  It uses the actual field

  F' = S1720Field = SplittingField (S1687H * (X^2 + 1))

and the actual profinite group

  G = Iut.AbsoluteGaloisProfinite F'.

## What is constructed

* S1734SmallGaloisCategory = Action FintypeCat.{0} G, with the actual
  Category.{0,1} structure inherited from Mathlib's action category;

* the Mathlib instances

    PreGaloisCategory (Action FintypeCat.{0} G),
    GaloisCategory (Action FintypeCat.{0} G),
    FiberFunctor (Action.forget FintypeCat.{0} G),
    FiberFunctor (forget₂ (Action FintypeCat.{0} G) FintypeCat.{0}),

  all obtained directly from CategoryTheory.Galois.Examples.  The bundled
  profinite group is coerced to its underlying type, whose Group instance is
  ProfiniteGrp.group; no continuity hypothesis is needed by these instances.

* the universe checks: the object type is in Type 1 and the hom type is in
  Type 0, so the category is indeed Category.{0,1}.

## The geometric comparison and the exact first missing field

S1734CoverType = Iut.OrbicurveFiniteEtaleCover S1726Orbicurve is the actual
type of representably finite-étale stack covers of the S1726 hyperbolic
orbicurve.  The tree provides no category instance on this type.  In
fact the canonical morphism type Iut.OrbicurveFiniteEtaleCoverMap A B is
declared in Type 1, while the geometric interface
Iut.OrbicurveEtaleFundamentalGroup asks for Category.{0,1} on the cover
type together with a bijective comparison to the actual cover maps.  The first
missing datum is therefore

  S1734FirstMissing = Category.{0,1} (OrbicurveFiniteEtaleCover S1726Orbicurve).

The underlying obstruction is the same one isolated in S1549/S1562: the
original small Hom field forces a Type 0 Hom carrier, while the actual cover
maps live in Type 1.  S1734SmallHomFirstMissing records the required small
carrier together with an equivalence to the actual cover maps; no Shrink,
ULift or arbitrary carrier is inserted.

S1734CandidateFiberFunctorData records exactly the additional data of a
candidate comparison functor

  Action FintypeCat.{0} G ⥤ OrbicurveFiniteEtaleCover S1726Orbicurve:

a chosen small cover category, an object map, a morphism map, and the identity
and composition laws.  No such datum is constructed here, and no equivalence
between the small Galois category and the cover type is asserted.  The
candidate is a datum, not a fake Galois correspondence.

## Honest boundary: abstract versus continuous actions

Mathlib's Galois.Examples is about the abstract group action category
Action FintypeCat G; it neither assumes nor asserts continuity of the action.
The tree's Iut.continuousAction... construction is the category of finite
continuous G-actions.  These are not definitionally the same category, and
this file does not assert an equivalence between them.  The geometric side of
the comparison is the continuous one, so identifying the two (or proving that
a specific abstract action is continuous) is a separate input and is not
supplied by Mathlib's abstract-action instances.

## Trust footprint

No placeholder or new assumption is used.  The dependency footprint is
checked at the end of the file.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1734ActionGaloisActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-! ## 1. The group, the small Galois category and its universes -/

/-- The absolute Galois group of the S1720 field, as an actual profinite group. -/
abbrev S1734G : ProfiniteGrp.{0} :=
  Iut.AbsoluteGaloisProfinite S1720Field

/-- The small category of finite G-sets. -/
abbrev S1734SmallGaloisCategory : Type 1 :=
  Action FintypeCat.{0} S1734G

/-- The Category.{0,1} structure on the small category, inherited from
Mathlib's action category. -/
@[reducible] def S1734Category : Category.{0,1} S1734SmallGaloisCategory :=
  inferInstance

/-- The object type, placed explicitly in Type 1. -/
abbrev S1734Obj : Type 1 :=
  S1734SmallGaloisCategory

/-- The hom type, placed explicitly in Type 0. -/
abbrev S1734Hom (X Y : S1734Obj) : Type :=
  X ⟶ Y

/-- The small category is a Category.{0,1}. -/
@[reducible] def S1734_category_universe : Category.{0,1} S1734Obj :=
  S1734Category

/-- The object type is definitionally in Type 1. -/
theorem S1734_obj_universe :
    (S1734Obj : Type 1) = S1734SmallGaloisCategory :=
  rfl

/-- The hom type is definitionally in Type 0. -/
theorem S1734_hom_universe (X Y : S1734Obj) :
    (S1734Hom X Y : Type) = (X ⟶ Y) :=
  rfl

/-! ## 2. Mathlib's Galois-category instances -/

/-- Mathlib's PreGaloisCategory instance for finite G-sets. -/
theorem S1734_preGaloisCategory :
    PreGaloisCategory S1734SmallGaloisCategory :=
  inferInstance

/-- Mathlib's GaloisCategory instance for finite G-sets. -/
theorem S1734_galoisCategory :
    GaloisCategory S1734SmallGaloisCategory :=
  inferInstance

/-- Mathlib's FiberFunctor instance for the forgetful functor. -/
theorem S1734_fiberFunctor :
    PreGaloisCategory.FiberFunctor
      (Action.forget FintypeCat.{0} S1734G) :=
  inferInstance

/-- The same fiber functor in its forget₂ presentation. -/
theorem S1734_fiberFunctor_forget₂ :
    PreGaloisCategory.FiberFunctor
      (forget₂ (Action FintypeCat.{0} S1734G) FintypeCat.{0}) :=
  inferInstance

/-- The three Mathlib instances apply directly to the bundled profinite group.
There is no missing PreGaloisCategory, GaloisCategory or FiberFunctor
instance for ProfiniteGrp-valued G; the bundled group is used through its
underlying type and its Group instance. -/
theorem S1734_mathlib_instances_direct :
    PreGaloisCategory S1734SmallGaloisCategory ∧
      GaloisCategory S1734SmallGaloisCategory ∧
        PreGaloisCategory.FiberFunctor
          (Action.forget FintypeCat.{0} S1734G) :=
  ⟨S1734_preGaloisCategory, S1734_galoisCategory, S1734_fiberFunctor⟩

/-! ## 3. The actual cover type and the first missing field -/

/-- The actual type of representably finite-étale covers of the S1726
hyperbolic orbicurve. -/
abbrev S1734CoverType : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S1726Orbicurve

/-- The canonical morphism type of the actual covers.  Its codomain is
Type 1; this is why a Category.{0,1} structure on S1734CoverType is a
genuine additional datum. -/
abbrev S1734CoverMap (A B : S1734CoverType) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- The canonical cover-morphism type lands in Type 1. -/
theorem S1734_coverMap_universe (A B : S1734CoverType) :
    (S1734CoverMap A B : Type 1) =
      Iut.OrbicurveFiniteEtaleCoverMap A B :=
  rfl

/-- The exact first missing field for the geometric comparison: a small
category structure on the actual cover type.  The tree supplies no such
instance. -/
abbrev S1734FirstMissing : Type 1 :=
  Category.{0,1} S1734CoverType

/-- The small Hom family underlying a Category.{0,1} instance on the cover
type.  It is a Type 0 family, which is exactly what the original interface
forces. -/
def S1734FirstMissing.homCarrier (C : S1734FirstMissing) :
    S1734CoverType → S1734CoverType → Type :=
  C.Hom

/-- The precise small-Hom obstruction (the S1549/S1562 form): a Type 0 Hom
carrier together with an equivalence to the actual cover maps.  The full
Category.{0,1} field additionally supplies identities, composition and the
category laws.  No such carrier is constructed here. -/
structure S1734SmallHomFirstMissing where
  /-- The small Hom carrier. -/
  Hom : S1734CoverType → S1734CoverType → Type
  /-- Its equivalence to the actual cover maps. -/
  homEquiv : ∀ A B : S1734CoverType, Hom A B ≃ S1734CoverMap A B

/-- The geometric interface whose coverCategory field is precisely
S1734FirstMissing.  No inhabitant is constructed in this file. -/
abbrev S1734OrbicurveGaloisData : Type 1 :=
  Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve S1734G

/-- The S1726 exact missing group datum, specialized to the S1720 absolute
Galois group.  No group, cover category or fiber functor is fabricated. -/
abbrev S1734OrbicurveFundamentalGroupData : Type 1 :=
  Iut.OrbicurveFundamentalGroupData S1726Orbicurve S1734G

/-- The full geometric datum supplies the first missing cover category.  This
is only a projection: the full geometric datum itself is not constructed. -/
@[reducible] def S1734OrbicurveGaloisData.coverCategoryFirstMissing
    (data : S1734OrbicurveGaloisData) : S1734FirstMissing :=
  data.coverCategory

@[simp]
theorem S1734OrbicurveGaloisData.coverCategoryFirstMissing_eq
    (data : S1734OrbicurveGaloisData) :
    data.coverCategoryFirstMissing = data.coverCategory :=
  rfl

/-! ## 4. Data of a candidate comparison/fiber functor -/

/-- The data of a candidate comparison functor from the Mathlib small Galois
category to the actual finite-étale covers of the S1726 orbicurve.

The fields are exactly:

* a small category structure on the actual cover type;
* a functor from Action FintypeCat.{0} G to that category, equivalently an
  object map, a morphism map and the identity/composition laws.

No inverse, unit, counit, or equivalence is included.  In particular this is
not a claim that the two categories are equivalent.

Terminology: a Mathlib FiberFunctor is a functor from a Galois category to
FintypeCat.  The candidate below has the cover type as its target, so it is a
comparison/inverse functor candidate, not itself an instance of
PreGaloisCategory.FiberFunctor.  Composing it with a geometric fiber functor
on the cover type would give the corresponding fiber section.

A geometric realization must additionally identify the chosen category's
homs with the actual cover maps, i.e. supply the data of
S1734SmallHomFirstMissing.  The candidate structure below does not include
that identification, so it is not by itself a geometric Galois
correspondence. -/
structure S1734CandidateFiberFunctorData where
  /-- The missing small category structure on the actual cover type. -/
  coverCategory : S1734FirstMissing
  /-- The candidate comparison functor. -/
  functor : letI := coverCategory
    S1734SmallGaloisCategory ⥤ S1734CoverType

namespace S1734CandidateFiberFunctorData

variable (data : S1734CandidateFiberFunctorData)

/-- The candidate object map. -/
def obj (X : S1734SmallGaloisCategory) : S1734CoverType :=
  letI := data.coverCategory
  data.functor.obj X

/-- The candidate morphism map. -/
def map {X Y : S1734SmallGaloisCategory} (f : X ⟶ Y) :
    letI := data.coverCategory
    data.obj X ⟶ data.obj Y := by
  letI := data.coverCategory
  exact data.functor.map f

/-- The candidate functor preserves identities. -/
theorem map_id (X : S1734SmallGaloisCategory) :
    letI := data.coverCategory
    data.map (𝟙 X) = 𝟙 (data.obj X) := by
  letI := data.coverCategory
  exact data.functor.map_id X

/-- The candidate functor preserves composition. -/
theorem map_comp {X Y Z : S1734SmallGaloisCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := data.coverCategory
    data.map (f ≫ g) = data.map f ≫ data.map g := by
  letI := data.coverCategory
  exact data.functor.map_comp f g

end S1734CandidateFiberFunctorData

/-- The full candidate datum: the missing cover category together with the
functor data.  This type has no constructed inhabitant in this file. -/
abbrev S1734CandidateFiberFunctorDatum : Type 1 :=
  S1734CandidateFiberFunctorData

/-- The candidate datum is a functor, not an equivalence: an inhabitant
contains no inverse functor, no unit/counit and no equivalence proof. -/
theorem S1734_candidate_is_functor_data
    (data : S1734CandidateFiberFunctorDatum) :
    letI := data.coverCategory
    Nonempty (S1734SmallGaloisCategory ⥤ S1734CoverType) :=
  ⟨data.functor⟩

/-! ## 5. Axiom footprint -/

#print axioms S1734_category_universe
#print axioms S1734_obj_universe
#print axioms S1734_hom_universe
#print axioms S1734_preGaloisCategory
#print axioms S1734_galoisCategory
#print axioms S1734_fiberFunctor
#print axioms S1734_fiberFunctor_forget₂
#print axioms S1734_mathlib_instances_direct
#print axioms S1734OrbicurveGaloisData.coverCategoryFirstMissing
#print axioms S1734OrbicurveGaloisData.coverCategoryFirstMissing_eq
#print axioms S1734CandidateFiberFunctorData.map_id
#print axioms S1734CandidateFiberFunctorData.map_comp
#print axioms S1734_coverMap_universe
#print axioms S1734_candidate_is_functor_data

end LeanFormal.IUT.XiFPaper.S1734ActionGaloisActual

end
