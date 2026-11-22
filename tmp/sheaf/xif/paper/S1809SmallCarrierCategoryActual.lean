/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1766CanonicalModelInjectivityActual

/-!
# S1809: the actual S1726 cover category is a Category.{0,1} with small homs

S1728 isolated the first missing categorical field of the target
OrbicurveEtaleFundamentalGroup S1726Orbicurve (AbsoluteGaloisProfinite S1726K),
namely

  coverCategory : Category.{0,1} (OrbicurveFiniteEtaleCover S1726Orbicurve),

and constructed a genuine Category.{1,1} on the actual cover type
(S1728ActualCategory11) whose homs are 2-isomorphism classes of actual cover
maps.  The literal raw cover-map type is Type 1, so the remaining problem was
smallness of the hom family.

S1766 then produced, unconditionally, the small model

  S1766QuotSmallCarrier A B = Set.range (S1766QuotAct A B) : Type

together with the equivalence

  S1766QuotSmallEquiv A B :
    Quot (S1728CoverMapRel A B) ≃ S1766QuotSmallCarrier A B,

because the canonical action is injective on the 2-isomorphism quotient.  This
file uses exactly that carrier and equivalence to transport the S1728
Category.{1,1} structure down to the target universe.

## Result

1. S1809CoverCategory01 : Category.{0,1} S1728Cover with
   Hom := S1766QuotSmallCarrier (literals: the hom family is the S1766
   small carrier, hence Type 0).  It is built by S1728's transport lemma
   S1728CategoryOfHomEquiv along S1766QuotSmallEquiv.  This is
   unconditional and inhabits the first missing categorical field of S1728
   (S1809CoverCategoryFirstMissing_inhabited,
   S1809TargetCoverCategory_inhabited).

2. S1809ComparisonFunctor: identity on objects and S1766QuotSmallEquiv on
   homs, from the new Category.{0,1} to S1728's 2-isomorphism quotient
   category.  It is Full, Faithful and EssSurj, hence an IsEquivalence
   (S1809ComparisonFunctor_isEquivalence).  The small category is therefore
   the actual quotient category at a smaller hom universe, not a stand-in.

3. The raw-cover-map requirement S1728SmallRawCoverDataRequired is NOT
   obtained from the small carrier.  Raw cover maps are genuinely Type 1
   (S1728CoverMap A B : Type 1 cannot be relaxed to Type 0), and the
   canonical construction of a raw small carrier from the quotient carrier
   needs exactly injectivity of the quotient map Quot.mk, equivalently a
   retraction of it, equivalently S1766's residual R2a
   S1766CoverMapDiscrete.  This file

   * names that datum S1809SmallRawCoverDataFirstMissing;
   * proves it is exactly S1766RawInjectivityExactMissing, exactly
     injectivity of Quot.mk, exactly the existence of a retraction of
     Quot.mk, and exactly raw R2a
     (S1744CanonicalModelHomActionInjective);
   * proves that it makes the quotient equivalent to the raw maps
     (S1809QuotEquivRaw) and therefore discharges S1728's raw requirement
     (S1809SmallRawCoverDataOfFirstMissing,
     S1809SmallRawCoverDataRequired_of_firstMissing).

   No inhabitant of S1728SmallRawCoverDataRequired is asserted.

The Galois field on top of the new category is recorded as
S1809GaloisCategoryRequired; it is not constructed.

## Honest boundary

No sorry, no new axiom, no Shrink, ULift, PLift or PUnit, and no fake
category: S1809CoverCategory01 is a kernel-checked Category.{0,1} whose
homs are the actual Type-0 2-isomorphism-class carrier and whose composition is
transported from the actual bicategorical composition.  The unconditional part
is the category and its equivalence to the quotient category; the conditional
part is exactly the raw smallness statement, gated by the named S1766 residual.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual

universe u

/-! ## 1. The small hom family and the transported category -/

/-- The hom family of the actual small cover category: the Type-0 subtype
S1766QuotSmallCarrier of the canonical-model hom types, i.e. the
2-isomorphism classes of actual finite-etale cover maps realised inside the
Type-0 model morphisms. -/
abbrev S1809SmallHom (A B : S1728Cover) : Type :=
  S1766QuotSmallCarrier A B

/-- The small hom family is equivalent to the actual 2-isomorphism quotient of
cover maps.  This is S1766's unconditional injectivity of the canonical action
on the quotient, packaged as an equivalence. -/
noncomputable abbrev S1809SmallHomEquiv (A B : S1728Cover) :
    S1809SmallHom A B ≃ (A ⟶ B) :=
  (S1766QuotSmallEquiv A B).symm

/-- **The target-universe cover category.**  A genuine Category.{0,1} on the
actual S1726 finite-etale cover type, obtained by transporting S1728's
2-isomorphism quotient category along the small hom equivalences
S1766QuotSmallEquiv.  Its homs are S1766QuotSmallCarrier, a Type 0 type.

This is unconditional: no discreteness hypothesis, no Shrink/ULift/PUnit,
and no redefinition of the objects. -/
@[reducible] noncomputable def S1809CoverCategory01 :
    Category.{0, 1} S1728Cover :=
  S1728CategoryOfHomEquiv (D := S1728Cover)
    (H := S1766QuotSmallCarrier)
    (fun A B => S1809SmallHomEquiv A B)

/-- The hom types of the actual small category are literally the Type-0 S1766
small carrier. -/
theorem S1809CoverCategory01_hom (A B : S1728Cover) :
    (@Quiver.Hom _ S1809CoverCategory01.toQuiver A B) = S1809SmallHom A B :=
  rfl

/-! ## 2. The small category is the actual quotient category -/

section

attribute [local instance] S1809CoverCategory01

/-- The comparison functor from the small-hom category to S1728's actual
2-isomorphism quotient category: the identity on objects and
S1766QuotSmallEquiv on homs. -/
noncomputable def S1809ComparisonFunctor :
    @CategoryTheory.Functor S1728Cover S1809CoverCategory01 S1728Cover
      (S1728CoverCategory11 (F := S1726K) (X := S1726Orbicurve)) where
  obj A := A
  map {A B} f := (S1766QuotSmallEquiv A B).symm f
  map_id A := by
    exact Equiv.apply_symm_apply _ _
  map_comp {A B C} f g := by
    exact Equiv.apply_symm_apply _ _

instance : S1809ComparisonFunctor.Full where
  map_surjective {A B} f :=
    ⟨(S1766QuotSmallEquiv A B) f, by
      exact Equiv.symm_apply_apply _ _⟩

instance : S1809ComparisonFunctor.Faithful where
  map_injective {A B} f g h := by
    exact (S1766QuotSmallEquiv A B).symm.injective h

instance : S1809ComparisonFunctor.EssSurj where
  mem_essImage A :=
    ⟨A, ⟨@CategoryTheory.Iso.refl S1728Cover
      (S1728CoverCategory11 (F := S1726K) (X := S1726Orbicurve)) A⟩⟩

/-- The comparison functor is an equivalence: the Category.{0,1} constructed
here is the actual 2-isomorphism quotient category of cover maps, transported
to the target hom universe. -/
instance S1809ComparisonFunctor_isEquivalence :
    S1809ComparisonFunctor.IsEquivalence where

end

/-! ## 3. The target fields -/

/-- S1728's first missing cover-category field is inhabited, unconditionally. -/
noncomputable def S1809CoverCategoryFirstMissing_inhabited :
    S1728CoverCategoryFirstMissing :=
  S1809CoverCategory01

/-- The same category inhabits the target's coverCategory field type. -/
noncomputable def S1809TargetCoverCategory_inhabited :
    S1728TargetCoverCategory :=
  S1809CoverCategory01

/-- The next field of the target on top of the cover category: the Galois
structure on the new Category.{0,1}.  No inhabitant is constructed here. -/
def S1809GaloisCategoryRequired : Prop :=
  @GaloisCategory.{1, 0} S1728Cover S1809CoverCategory01

/-! ## 4. Raw cover maps and the exact first missing datum -/

/-- The raw cover-map type of the S1726 orbicurve is Type 1 (S1728CoverMap is a
structure of strong transformations over the large base site); it cannot be the
hom family of a Category.{0,1}.  The declaration
S1728CoverMap : S1728Cover -> S1728Cover -> Type 1 in S1728 is re-checked
here. -/
example (A B : S1728Cover) : Type 1 := S1728CoverMap A B

/-- The equivalence closure of the 2-isomorphism relation is the relation
itself.  This converts equality of quotient classes back into a
2-isomorphism. -/
theorem S1809EqvGen_to_rel {α : Type u} {r : α → α → Prop} (hr : Equivalence r)
    {f g : α} (h : Relation.EqvGen r f g) : r f g := by
  induction h with
  | rel x y hxy => exact hxy
  | refl x => exact hr.refl x
  | symm x y _ ih => exact hr.symm ih
  | trans x y z _ _ ih1 ih2 => exact hr.trans ih1 ih2

/-- **The exact first missing datum** for S1728's raw small cover data on the
canonical small-carrier route: injectivity of the 2-isomorphism quotient map,
i.e. every 2-isomorphism class of cover maps is a singleton.  This is exactly
S1766's residual R2a, not a new geometric input. -/
def S1809SmallRawCoverDataFirstMissing : Prop :=
  S1766CoverMapDiscrete

/-- The named first missing datum is exactly S1766's named residual. -/
theorem S1809SmallRawCoverDataFirstMissing_iff_S1766 :
    S1809SmallRawCoverDataFirstMissing ↔ S1766RawInjectivityExactMissing :=
  Iff.rfl

/-- It is exactly injectivity of the quotient map on cover maps. -/
theorem S1809SmallRawCoverDataFirstMissing_iff_quotMk_injective :
    S1809SmallRawCoverDataFirstMissing ↔
      ∀ A B : S1728Cover,
        Function.Injective
          (Quot.mk (fun f g : S1728CoverMap A B => S1728CoverMapRel f g)) := by
  constructor
  · intro h A B f g hq
    exact h A B f g
      (S1809EqvGen_to_rel (S1728CoverMapRel_equivalence A B)
        (Quot.eqvGen_exact hq))
  · intro h A B f g hrel
    exact h A B (Quot.sound hrel)

/-- It is exactly the existence of a retraction of the quotient map, i.e. a
choice of one representative per 2-isomorphism class. -/
theorem S1809SmallRawCoverDataFirstMissing_iff_section :
    S1809SmallRawCoverDataFirstMissing ↔
      (∀ A B : S1728Cover,
        ∃ s : Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) →
            S1728CoverMap A B,
          ∀ f, s (Quot.mk _ f) = f) := by
  constructor
  · intro h A B
    exact ⟨Quot.lift id (fun f g hrel => h A B f g hrel), fun f => rfl⟩
  · rintro h A B f g hrel
    obtain ⟨s, hs⟩ := h A B
    calc f = s (Quot.mk _ f) := (hs f).symm
      _ = s (Quot.mk _ g) := by rw [Quot.sound hrel]
      _ = g := hs g

/-- It is exactly S1744's raw injectivity R2a of the canonical action. -/
theorem S1809SmallRawCoverDataFirstMissing_iff_rawInjective :
    S1809SmallRawCoverDataFirstMissing ↔
      S1744CanonicalModelHomActionInjective S1744CanonicalModelHomActionActual :=
  S1766_raw_injective_iff_discrete.symm

/-- Under the first missing datum, the 2-isomorphism quotient is equivalent to
the raw cover maps: pick the chosen representative of each class. -/
noncomputable def S1809QuotEquivRaw
    (h : S1809SmallRawCoverDataFirstMissing) (A B : S1728Cover) :
    Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) ≃
      S1728CoverMap A B where
  toFun := Quot.lift id (fun f g hrel => h A B f g hrel)
  invFun := Quot.mk _
  left_inv q := by
    induction q using Quot.inductionOn with
    | h f => rfl
  right_inv f := rfl

/-- The raw small cover datum for every pair of actual covers, from the first
missing datum.  The carrier is the S1766 Type-0 small carrier. -/
noncomputable def S1809SmallRawCoverDataOfFirstMissing
    (h : S1809SmallRawCoverDataFirstMissing) (A B : S1728Cover) :
    S1728ActualSmallRawCoverData A B where
  Carrier := S1766QuotSmallCarrier A B
  equiv := (S1766QuotSmallEquiv A B).symm.trans (S1809QuotEquivRaw h A B)

/-- **The exact first missing datum discharges S1728's small raw cover data.**
No unconditional inhabitant of S1728SmallRawCoverDataRequired is claimed. -/
theorem S1809SmallRawCoverDataRequired_of_firstMissing
    (h : S1809SmallRawCoverDataFirstMissing) :
    S1728SmallRawCoverDataRequired :=
  fun A B => ⟨S1809SmallRawCoverDataOfFirstMissing h A B⟩

/-! ## 5. Checks and axiom audit -/

#check S1809SmallHom
#check S1809SmallHomEquiv
#check S1809CoverCategory01
#check S1809CoverCategory01_hom
#check S1809ComparisonFunctor
#check S1809ComparisonFunctor_isEquivalence
#check S1809CoverCategoryFirstMissing_inhabited
#check S1809TargetCoverCategory_inhabited
#check S1809GaloisCategoryRequired
#check S1809EqvGen_to_rel
#check S1809SmallRawCoverDataFirstMissing
#check S1809SmallRawCoverDataFirstMissing_iff_S1766
#check S1809SmallRawCoverDataFirstMissing_iff_quotMk_injective
#check S1809SmallRawCoverDataFirstMissing_iff_section
#check S1809SmallRawCoverDataFirstMissing_iff_rawInjective
#check S1809QuotEquivRaw
#check S1809SmallRawCoverDataOfFirstMissing
#check S1809SmallRawCoverDataRequired_of_firstMissing

#print axioms S1809CoverCategory01
#print axioms S1809CoverCategory01_hom
#print axioms S1809ComparisonFunctor
#print axioms S1809ComparisonFunctor_isEquivalence
#print axioms S1809CoverCategoryFirstMissing_inhabited
#print axioms S1809EqvGen_to_rel
#print axioms S1809SmallRawCoverDataFirstMissing_iff_quotMk_injective
#print axioms S1809SmallRawCoverDataFirstMissing_iff_section
#print axioms S1809SmallRawCoverDataFirstMissing_iff_rawInjective
#print axioms S1809QuotEquivRaw
#print axioms S1809SmallRawCoverDataOfFirstMissing
#print axioms S1809SmallRawCoverDataRequired_of_firstMissing

end LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
