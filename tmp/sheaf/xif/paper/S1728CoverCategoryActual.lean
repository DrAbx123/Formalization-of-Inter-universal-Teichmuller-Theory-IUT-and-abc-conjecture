/-
# S1728: actual small Galois category for the S1726 D6 orbicurve

## Question

The D6 orbicurve of S1726 is missing the datum

  Iut.OrbicurveFundamentalGroupData S1726Orbicurve
    (Iut.AbsoluteGaloisProfinite S1726K).

Its OrbicurveEtaleFundamentalGroup field asks for

  coverCategory : Category.{0} (OrbicurveFiniteEtaleCover S1726Orbicurve)
  galoisCategory : @GaloisCategory ... coverCategory

Because the orbicurve lives over S1726K : Type, the object type is Type 1
and the field is literally Category.{0, 1}: objects in Type 1, homs in
Type 0.  S1641 constructed composition and identity of the actual cover maps
but its raw map type is Type 1, and its naive strict laws are not available.

This file analyses the three proposed ways around the size issue, without
Shrink, ULift, PLift or PUnit:

1. quotient the actual cover maps by 2-isomorphism classes;
2. build a small model of finite connected covers;
3. truncate with Core or Pith.

## Result

* The 2-isomorphism quotient does remove the strictness obstruction: the
  category whose hom-types are 2-isomorphism classes of the underlying strong
  transformations is an actual Category.{1,1} on the actual cover type.
  The strict unitor/associator equalities demanded by S1641 are replaced by
  2-isomorphisms, and the quotient makes those isomorphisms actual equalities.
  This is a genuine category, not a fake one, but its hom-types are still
  Type 1.

* Quot, Core and Pith preserve the ambient universe.  A quotient of a
  Type 1 type is Type 1; Core C has the same object and hom universes as C;
  Pith B has the same object universe as B, and its 1-cells are
  Core (a ->> b), hence live in the same universe as the 1-cells of B.
  None of these operations alone produces the Type 0 hom required by the
  target.

* A Category.{0,1} on the actual cover type is constructed from an
  explicit small raw cover-map carrier: for every pair of covers, a Type 0
  type with an equivalence to the actual cover-map type.  The 2-isomorphism
  quotient of a small carrier is small, and the quotient category structure
  transports across the resulting equivalence.  This is a real construction,
  conditional only on the small carriers; no Shrink/ULift is used.

* No such small raw cover-map carrier is constructed here.  The target itself
  implies one: an OrbicurveEtaleFundamentalGroup stores a small hom-type
  and a bijection to the actual cover maps (coverMorphism_bijective).  Thus
  the missing smallness is a necessary input, not an optional convenience.

* The geometric input that supplies it is the paper's connected-cover
  smallness/classification: connectedness of the orbicurve plus the
  classification of finite etale covers by finite separable extensions of the
  function field / by finite quotients of the etale fundamental group.  It is
  recorded below as S1728SmallGaloisModel, together with the conditional
  category construction.  No inhabitant and no GaloisCategory for the actual
  orbicurve are asserted.

## Honest boundary

No sorry, no axiom, no Shrink, no ULift, no PUnit, and no fake
Category or GaloisCategory is introduced.  The unconditional
Category.{1,1} is a genuine category on the actual cover type.  The
conditional Category.{0,1} is a genuine category constructed from explicit
small hom data.  The target OrbicurveEtaleFundamentalGroup remains missing.
-/

import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

/-! ## 1. The 2-isomorphism quotient of the actual cover maps -/

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- Two actual cover maps are identified when their underlying strong
transformations are 2-isomorphic.  This is the homotopy relation of the
bicategory of etale stacks, restricted to cover maps. -/
def S1728CoverMapRel {A B : OrbicurveFiniteEtaleCover X}
    (f g : OrbicurveFiniteEtaleCoverMap A B) : Prop :=
  Nonempty (f.map ≅ g.map)

theorem S1728CoverMapRel_refl {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) : S1728CoverMapRel f f :=
  ⟨Iso.refl f.map⟩

theorem S1728CoverMapRel_symm {A B : OrbicurveFiniteEtaleCover X}
    {f g : OrbicurveFiniteEtaleCoverMap A B}
    (h : S1728CoverMapRel f g) : S1728CoverMapRel g f := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem S1728CoverMapRel_trans {A B : OrbicurveFiniteEtaleCover X}
    {f g h : OrbicurveFiniteEtaleCoverMap A B}
    (hfg : S1728CoverMapRel f g) (hgh : S1728CoverMapRel g h) :
    S1728CoverMapRel f h := by
  rcases hfg with ⟨e1⟩
  rcases hgh with ⟨e2⟩
  exact ⟨e1.trans e2⟩

theorem S1728CoverMapRel_equivalence (A B : OrbicurveFiniteEtaleCover X) :
    Equivalence (S1728CoverMapRel (A := A) (B := B)) :=
  ⟨S1728CoverMapRel_refl, S1728CoverMapRel_symm, S1728CoverMapRel_trans⟩

/-- The quotient of cover maps by 2-isomorphism of the underlying strong
transformations.  For F : Type u the cover-map type is Type (u+1), so the
quotient is Type (u+1); it is not lowered. -/
abbrev S1728CoverMapClass (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  Quot (fun f g : OrbicurveFiniteEtaleCoverMap A B => S1728CoverMapRel f g)

/-! ### Whiskering, associativity and unit isomorphisms

These are the actual 2-isomorphisms used to prove that composition and identity
descend to 2-isomorphism classes.  They are the same components as in S1641,
but here they are used only to produce equalities of quotient classes, so no
strict unitor/associator equality is required. -/

noncomputable def S1728WhiskerLeftIso {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g g' : OrbicurveFiniteEtaleCoverMap B C)
    (eg : g.map ≅ g'.map) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp f.map g.map)
      (Pseudofunctor.StrongTrans.vcomp f.map g'.map) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  let fmap : source ⟶ mid := f.map
  let gmap : mid ⟶ target := g.map
  let gmap' : mid ⟶ target := g'.map
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target fmap gmap gmap' eg

noncomputable def S1728WhiskerRightIso {A B C : OrbicurveFiniteEtaleCover X}
    (f f' : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (ef : f.map ≅ f'.map) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp f.map g.map)
      (Pseudofunctor.StrongTrans.vcomp f'.map g.map) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  let fmap : source ⟶ mid := f.map
  let fmap' : source ⟶ mid := f'.map
  let gmap : mid ⟶ target := g.map
  exact @Bicategory.whiskerRightIso Bicat _ source mid target fmap fmap' ef gmap

noncomputable def S1728AssociatorIso {A B C D : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) h.map)
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map h.map)) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid1 : Bicat := B.source.fiber
  let mid2 : Bicat := C.source.fiber
  let target : Bicat := D.source.fiber
  let fmap : source ⟶ mid1 := f.map
  let gmap : mid1 ⟶ mid2 := g.map
  let hmap : mid2 ⟶ target := h.map
  exact @Bicategory.associator Bicat _ source mid1 mid2 target fmap gmap hmap

noncomputable def S1728LeftUnitorIso {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id A.source.fiber) f.map)
      f.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let target : Bicat := B.source.fiber
  let fmap : source ⟶ target := f.map
  exact @Bicategory.leftUnitor Bicat _ source target fmap

noncomputable def S1728RightUnitorIso {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.id B.source.fiber))
      f.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let target : Bicat := B.source.fiber
  let fmap : source ⟶ target := f.map
  exact @Bicategory.rightUnitor Bicat _ source target fmap

/-! ### Composition and identity on quotient classes -/

theorem S1728CoverMapRel_comp_right {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    {g g' : OrbicurveFiniteEtaleCoverMap B C}
    (hg : S1728CoverMapRel g g') :
    S1728CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f g') := by
  rcases hg with ⟨eg⟩
  exact ⟨by
    simpa only [S1641CoverMapComp_map] using S1728WhiskerLeftIso f g g' eg⟩

theorem S1728CoverMapRel_comp_left {A B C : OrbicurveFiniteEtaleCover X}
    {f f' : OrbicurveFiniteEtaleCoverMap A B}
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (hf : S1728CoverMapRel f f') :
    S1728CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f' g) := by
  rcases hf with ⟨ef⟩
  exact ⟨by
    simpa only [S1641CoverMapComp_map] using S1728WhiskerRightIso f f' g ef⟩

noncomputable def S1728CoverMapClassComp {A B C : OrbicurveFiniteEtaleCover X}
    (f : S1728CoverMapClass (A := A) (B := B))
    (g : S1728CoverMapClass (A := B) (B := C)) :
    S1728CoverMapClass (A := A) (B := C) :=
  Quot.map₂ (fun f g => S1641CoverMapComp f g)
    (fun _ _ _ hg => S1728CoverMapRel_comp_right _ hg)
    (fun _ _ _ hf => S1728CoverMapRel_comp_left _ hf) f g

noncomputable def S1728CoverMapClassId (A : OrbicurveFiniteEtaleCover X) :
    S1728CoverMapClass (A := A) (B := A) :=
  Quot.mk _ (S1641CoverMapId A)

@[reducible] noncomputable def S1728CoverCategoryStruct11 :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := S1728CoverMapClass
  id := S1728CoverMapClassId
  comp := S1728CoverMapClassComp

/-- The 2-isomorphism quotient is an actual category at the corrected universe:
objects Type (u+1), homs Type (u+1).  Its strict category laws are the
bicategory unitors and associator, transported through the quotient. -/
noncomputable instance S1728CoverCategory11 :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) where
  toCategoryStruct := S1728CoverCategoryStruct11
  id_comp := by
    intro A B f
    induction f using Quot.inductionOn with
    | h f =>
        apply Quot.sound
        exact ⟨by
          simpa only [S1728CoverCategoryStruct11, S1728CoverMapClassComp,
            S1728CoverMapClassId, S1641CoverMapComp_map, S1641CoverMapId_map,
            Quot.map₂_mk] using S1728LeftUnitorIso f⟩
  comp_id := by
    intro A B f
    induction f using Quot.inductionOn with
    | h f =>
        apply Quot.sound
        exact ⟨by
          simpa only [S1728CoverCategoryStruct11, S1728CoverMapClassComp,
            S1728CoverMapClassId, S1641CoverMapComp_map, S1641CoverMapId_map,
            Quot.map₂_mk] using S1728RightUnitorIso f⟩
  assoc := by
    intro A B C D f g h
    induction f using Quot.inductionOn with
    | h f =>
      induction g using Quot.inductionOn with
      | h g =>
        induction h using Quot.inductionOn with
        | h h =>
          apply Quot.sound
          exact ⟨by
            simpa only [S1728CoverCategoryStruct11, S1728CoverMapClassComp,
              S1641CoverMapComp_map, Quot.map₂_mk] using S1728AssociatorIso f g h⟩

/-! ## 2. Universe-preservation facts for the proposed truncations -/

/-- Quot of a type in Type (u+1) is again in Type (u+1).  This is the formal
reason why quotienting CoverMap by 2-isomorphism classes does not by itself
lower the hom universe. -/
abbrev S1728QuotUniverse (alpha : Type (u + 1)) (r : alpha → alpha → Prop) :
    Type (u + 1) :=
  Quot r

/-- Core preserves the object universe, hence cannot turn Type 1 objects into
Type 0 objects. -/
abbrev S1728CoreObject (C : Type (u + 1)) [Category.{u + 1, u + 1} C] :
    Type (u + 1) :=
  CategoryTheory.Core C

/-- The hom of Core C is CoreHom, living in the same universe as the hom of C;
in the cover case this is again Type 1. -/
abbrev S1728CoreHom {C : Type (u + 1)} [Category.{u + 1, u + 1} C]
    (X Y : S1728CoreObject C) : Type (u + 1) :=
  CategoryTheory.CoreHom X Y

/-- Pith B preserves the object universe of the bicategory B. -/
abbrev S1728PithObject (F : Type u) [Field F] : Type (u + 1) :=
  CategoryTheory.Bicategory.Pith (EtaleStackPseudofunctor F)

/-- A Pith 1-cell is Core (a -> b), so its universe is the 1-cell universe of
the original bicategory.  For the etale-stack bicategory this is Type 1 when
F : Type. -/
example (F : Type u) [Field F] (a b : S1728PithObject F) : Type (u + 1) :=
  a ⟶ b

/-! ## 3. Conditional category at the target universe -/

/-- A general quotient-equivalence lemma: quotienting a small carrier by a
relation pulled back along an equivalence gives the same quotient. -/
def S1728QuotCongrEquiv {alpha : Type (u + 1)} {beta : Type u}
    (r : alpha → alpha → Prop) (hr : Equivalence r) (e : beta ≃ alpha) :
    Quot (fun (x y : beta) => r (e x) (e y)) ≃ Quot r where
  toFun := Quot.lift (fun x => Quot.mk r (e x)) (fun x y h => Quot.sound h)
  invFun := Quot.lift
    (fun a => Quot.mk (fun (x y : beta) => r (e x) (e y)) (e.symm a))
    (fun a b h => by
      apply Quot.sound
      simpa using h)
  left_inv q := by
    induction q using Quot.inductionOn with
    | h x =>
      apply Quot.sound
      simpa using hr.refl (e x)
  right_inv q := by
    induction q using Quot.inductionOn with
    | h a =>
      apply Quot.sound
      simpa using hr.refl a

/-- Transport a category structure along a family of equivalences of hom-types.
The object type is unchanged; only the hom carrier is replaced by the small
model. -/
@[reducible] noncomputable def S1728CategoryOfHomEquiv
    (D : Type (u + 1)) [Category.{u + 1, u + 1} D]
    (H : D → D → Type u)
    (e : ∀ A B, H A B ≃ (A ⟶ B)) :
    Category.{u, u + 1} D where
  Hom := H
  id A := (e A A).symm (𝟙 A)
  comp {A B C} f g := (e A C).symm ((e A B f) ≫ (e B C g))
  id_comp {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.id_comp (f := e A B f)
  comp_id {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.comp_id (f := e A B f)
  assoc {A B C E} f g h := by
    apply (e A E).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.assoc (f := e A B f) (g := e B C g) (h := e C E h)

/-- Small raw cover-map data: a Type u carrier for each actual cover-map type,
with an equivalence to the actual maps. -/
structure S1728SmallRawCoverData (A B : OrbicurveFiniteEtaleCover X) where
  Carrier : Type u
  equiv : Carrier ≃ OrbicurveFiniteEtaleCoverMap A B

/-- The target implies small raw cover-map data: the stored coverCategory.Hom
is a Type u carrier, and coverMorphism_bijective gives the equivalence. -/
noncomputable def S1728SmallRawCoverDataOfEtaleFundamentalGroup
    {G : ProfiniteGrp.{u}}
    (data : OrbicurveEtaleFundamentalGroup X G)
    (A B : OrbicurveFiniteEtaleCover X) :
    S1728SmallRawCoverData (F := F) (X := X) A B := by
  letI := data.coverCategory
  exact
    { Carrier := (A ⟶ B)
      equiv := Equiv.ofBijective
        (fun map : A ⟶ B =>
          ({ map := data.coverMorphism map,
             commutes := data.coverMorphism_over map } :
            OrbicurveFiniteEtaleCoverMap A B))
        (data.coverMorphism_bijective (source := A) (target := B)) }

/-- From a small raw cover-map family, the 2-isomorphism quotient is a small
carrier (Type u) equivalent to the actual quotient, and the quotient category
structure transports to the actual cover type at the target universe
Category.{u, u+1}.  For F : Type this is Category.{0,1}. -/
@[reducible] noncomputable def S1728CategoryOfSmallRawCoverData
    (H : (A B : OrbicurveFiniteEtaleCover X) → Type u)
    (e : ∀ A B, H A B ≃ OrbicurveFiniteEtaleCoverMap A B) :
    Category.{u, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CategoryOfHomEquiv
    (D := OrbicurveFiniteEtaleCover X)
    (H := fun A B =>
      Quot (fun f g : H A B => S1728CoverMapRel (e A B f) (e A B g)))
    (fun A B =>
      S1728QuotCongrEquiv (S1728CoverMapRel (A := A) (B := B))
        (S1728CoverMapRel_equivalence A B) (e A B))

/-! ## 4. The S1726 D6 orbicurve -/

namespace S1728Paper

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-- The actual cover type of the S1726 D6 orbicurve. -/
abbrev S1728Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S1726Orbicurve

/-- The actual cover-map type of the S1726 D6 orbicurve. -/
abbrev S1728CoverMap (A B : S1728Cover) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- The target's `Category.{0,1}` has a Type 0 hom family. -/
example (C : Category.{0, 1} S1728Cover) (A B : S1728Cover) : Type :=
  @Quiver.Hom _ C.toQuiver A B

/-- The actual cover-map type is Type 1, so it cannot literally be the hom
family of `Category.{0,1}`.  A small carrier with an equivalence is required. -/
example (A B : S1728Cover) : Type 1 := S1728CoverMap A B

/-- The actual 2-isomorphism quotient category on the S1726 cover type, at the
corrected universe Category.{1,1}.  This is not the target Category.{0,1};
the hom-types are still Type 1. -/
@[reducible] noncomputable def S1728ActualCategory11 : Category.{1,1} S1728Cover :=
  S1728CoverCategory11 (F := S1726K) (X := S1726Orbicurve)

/-- The actual small raw cover-map data for the S1726 cover type. -/
abbrev S1728ActualSmallRawCoverData (A B : S1728Cover) : Type 1 :=
  S1728SmallRawCoverData (F := S1726K) (X := S1726Orbicurve) A B

/-- Conditional actual Category.{0,1} on the S1726 cover type: it is enough to
provide a small raw cover-map carrier for every pair.  This is a genuine
category at exactly the target universe; it is not an inhabitant of the target
because no such family is constructed. -/
@[reducible] noncomputable def S1728ActualCategory01
    (H : (A B : S1728Cover) → Type)
    (e : ∀ A B, H A B ≃ S1728CoverMap A B) :
    Category.{0, 1} S1728Cover :=
  S1728CategoryOfSmallRawCoverData
    (F := S1726K) (X := S1726Orbicurve) H e

/-- The target's coverCategory field type. -/
def S1728TargetCoverCategory : Type 1 :=
  Category.{0, 1} S1728Cover

/-- The target's galoisCategory field type, for a given cover category. -/
def S1728TargetGaloisCategory (C : S1728TargetCoverCategory) : Prop :=
  @GaloisCategory.{1, 0} S1728Cover C

/-- The two fields of the target that this file analyses.  No inhabitant is
constructed. -/
structure S1728CoverCategoryAndGalois where
  coverCategory : Category.{0, 1} S1728Cover
  galoisCategory : @GaloisCategory.{1, 0} S1728Cover coverCategory

/-- Every full OrbicurveEtaleFundamentalGroup certificate has this pair as its
literal coverCategory/galoisCategory fields. -/
noncomputable def S1728CoverCategoryAndGaloisOfEtalePi
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G) :
    S1728CoverCategoryAndGalois where
  coverCategory := D.coverCategory
  galoisCategory := D.galoisCategory

/-- Small cover-model input: the paper's connected-cover classification.  A
small object type of covers, with a small category structure, equivalences on
objects and homs, and a Galois-category structure.  This is the geometric input
that the connected-cover smallness theorem is expected to supply; it is not
constructed. -/
structure S1728SmallGaloisModel where
  SmallCover : Type
  category : Category.{0, 0} SmallCover
  objEquiv : SmallCover ≃ S1728Cover
  homEquiv : ∀ a b : SmallCover,
    @Quiver.Hom _ category.toQuiver a b ≃
      S1728CoverMap (objEquiv a) (objEquiv b)
  galoisCategory : @GaloisCategory.{0, 0} SmallCover category

/-- The small hom family induced by a small Galois model: homs between the
chosen small preimages of the two actual covers. -/
noncomputable def S1728SmallRawFamilyOfSmallGaloisModel
    (M : S1728SmallGaloisModel) (A B : S1728Cover) : Type :=
  @Quiver.Hom _ M.category.toQuiver (M.objEquiv.symm A) (M.objEquiv.symm B)

/-- The small hom family of a small Galois model is equivalent to the actual
cover-map type, by transporting the model's hom equivalence along the chosen
preimages. -/
noncomputable def S1728SmallRawEquivOfSmallGaloisModel
    (M : S1728SmallGaloisModel) (A B : S1728Cover) :
    S1728SmallRawFamilyOfSmallGaloisModel M A B ≃ S1728CoverMap A B := by
  let a : M.SmallCover := M.objEquiv.symm A
  let b : M.SmallCover := M.objEquiv.symm B
  have hA : M.objEquiv a = A := M.objEquiv.apply_symm_apply A
  have hB : M.objEquiv b = B := M.objEquiv.apply_symm_apply B
  exact (M.homEquiv a b).trans (Equiv.cast (by rw [hA, hB]))

/-- The small raw cover-map datum obtained from a small Galois model. -/
noncomputable def S1728SmallRawCoverDataOfSmallGaloisModel
    (M : S1728SmallGaloisModel) (A B : S1728Cover) :
    S1728ActualSmallRawCoverData A B where
  Carrier := S1728SmallRawFamilyOfSmallGaloisModel M A B
  equiv := S1728SmallRawEquivOfSmallGaloisModel M A B

/-- The paper's small Galois model yields a genuine `Category.{0,1}` on the
actual S1726 cover type.  This fills the categorical field of the target; the
Galois field and the geometric realization fields remain separate. -/
@[reducible] noncomputable def S1728ActualCategory01OfSmallGaloisModel
    (M : S1728SmallGaloisModel) : Category.{0, 1} S1728Cover :=
  S1728ActualCategory01
    (S1728SmallRawFamilyOfSmallGaloisModel M)
    (S1728SmallRawEquivOfSmallGaloisModel M)

/-- The exact first missing smallness datum for the categorical part: for every
pair of actual covers, a Type 0 carrier equivalent to the actual cover-map
type.  This is precisely what the target's coverMorphism_bijective forces. -/
def S1728SmallRawCoverDataRequired : Prop :=
  ∀ A B : S1728Cover, Nonempty (S1728ActualSmallRawCoverData A B)

/-- A small Galois model supplies the exact first missing smallness datum. -/
theorem S1728SmallRawCoverDataRequiredOfSmallGaloisModel
    (M : S1728SmallGaloisModel) : S1728SmallRawCoverDataRequired :=
  fun A B => ⟨S1728SmallRawCoverDataOfSmallGaloisModel M A B⟩

/-- The exact first missing categorical field of the target. -/
def S1728CoverCategoryFirstMissing : Type 1 :=
  Category.{0, 1} S1728Cover

/-- The exact first missing Galois field of the target. -/
abbrev S1728GaloisCategoryFirstMissing : Type 1 :=
  S1728CoverCategoryAndGalois

/-- The full target implies the small raw cover-map data.  Therefore the
smallness is necessary for any solution, not merely a convenient route. -/
theorem S1728SmallRawCoverDataOfEtalePi
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G) :
    S1728SmallRawCoverDataRequired :=
  fun A B =>
    ⟨S1728SmallRawCoverDataOfEtaleFundamentalGroup
      (F := S1726K) (X := S1726Orbicurve) D A B⟩

#check S1728Cover
#check S1728CoverMap
#check S1728ActualCategory11
#check S1728ActualCategory01
#check S1728TargetCoverCategory
#check S1728TargetGaloisCategory
#check S1728CoverCategoryAndGalois
#check S1728CoverCategoryAndGaloisOfEtalePi
#check S1728SmallGaloisModel
#check S1728SmallRawCoverDataOfSmallGaloisModel
#check S1728SmallRawCoverDataRequiredOfSmallGaloisModel
#check S1728ActualCategory01OfSmallGaloisModel
#check S1728SmallRawCoverDataRequired
#check S1728CoverCategoryFirstMissing
#check S1728GaloisCategoryFirstMissing
#check S1728SmallRawCoverDataOfEtalePi

#print axioms S1728ActualCategory11
#print axioms S1728SmallRawCoverDataOfEtaleFundamentalGroup
#print axioms S1728ActualCategory01
#print axioms S1728CoverCategoryAndGaloisOfEtalePi
#print axioms S1728ActualCategory01OfSmallGaloisModel
#print axioms S1728SmallRawCoverDataRequiredOfSmallGaloisModel

end S1728Paper

end LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual

end
