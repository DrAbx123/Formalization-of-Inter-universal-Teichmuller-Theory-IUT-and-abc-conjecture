/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1741AutFiberActual
import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# S1754: actual field values and exact residuals for OrbicurveEtaleFundamentalGroup

## Question

The D6 source clause needs an inhabitant of

  Iut.OrbicurveFundamentalGroupData S1726Orbicurve (Iut.AbsoluteGaloisProfinite S1726K),

whose first ingredient is a datum

  D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G,   G : ProfiniteGrp.{0}.

S1737 filled the two base fields (baseScheme = S1726AffineOver = Spec R', basePoint = the
identity strong transformation).  S1740 showed that such a datum gives
Cover ≌ ContAction, and that the S1726 stack is exactly the representable pseudofunctor of
S1726AffineOver.  This file does not postulate a datum: it determines, field by field, which of
the remaining fields can actually be constructed from the already available inputs and which are
genuinely missing.

## Results

1. The action field and the isFundamentalGroup field are constructed from ONE comparison datum.

   For any Galois category C, fiber functor F, and group G, s1754ActionOfMonoidHom e turns
   e : G →* Aut F into an actual action of G on every fiber of F (MulAction.compHom applied to
   Mathlib's evaluation action of Aut F; the action identification is rfl).  For a continuous
   group isomorphism e : G ≃ₜ* Aut F, s1754IsFundamentalGroupOfContinuousMulEquiv proves
   PreGaloisCategory.IsFundamentalGroup F G for that action, by S1741's transport theorem.
   Thus the two group-theoretic fields are not independent data: they are exactly the single
   continuous comparison G ≃ₜ* Aut F.

2. The three object-level categorical fields are EXACTLY a family of bijections of the hom types
   with the actual cover maps:

     Nonempty S1754CoverMapRealization
       ↔ ∀ A B, Nonempty ((A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B).

   (The converse direction chooses the equivalences with Classical.choice.)

3. The two coherence fields extend item 2 to a strict hom-wise realization:

     Nonempty S1754StrictCoverMapRealization ↔ Nonempty S1754StrictHomEquiv,

   where S1754StrictHomEquiv is a family of equivalences to the actual cover maps compatible with
   identities and composition up to 2-isomorphism.  This is the exact residual for the five
   categorical fields.

4. Conversely, every actual datum yields that continuous comparison: for a datum D,
   s1754ContinuousMulEquivOfData D : (G : Type u) ≃ₜ* Aut D.fiber, built from Mathlib's
   toAutHomeo and toAutMulEquiv under D's own IsFundamentalGroup.  Together with item 1 this
   makes the two group-theoretic fields exactly equivalent to Residual 3.  Likewise the fiber
   identification of a datum is literally the fiberIdentification field
   (s1754FiberIdentificationOfData), so Residual 2 is exactly that field, not more.

5. geometricFiberFintype is NOT independent: it is derived from fiberIdentification.
   s1754GeometricFiberFintypeOfIdentification turns any object-level equivalence between the
   chosen fiber functor and the literal CostructuredArrow geometric fiber into a Fintype instance
   on the geometric fiber (FintypeCat.fintype transported along the equivalence).  Hence the full
   datum is constructible from the reduced piece list S1754Pieces, and

     Nonempty S1754Pieces ↔ Nonempty (Iut.OrbicurveEtaleFundamentalGroup X G).

6. Each piece list supplies S1728's small raw cover-map data with the categorical hom type as the
   carrier (S1754Pieces.smallRawCoverData), so the categorical residual is consistent with the
   S1728 smallness analysis: the five categorical fields force exactly such a small carrier.

## Field-by-field status for the S1726 datum

* baseScheme, basePoint: ACTUAL (S1737; reproduced as S1754S1726BaseScheme and
  S1754S1726BasePoint).
* coverCategory: MISSING.  Category.{0} on a Type 1 cover type whose actual hom type is Type 1
  (S1728); only conditional constructions from small raw cover data exist.
* galoisCategory: MISSING; depends on coverCategory.
* fiber, fiberFunctor: MISSING; no functor from the actual cover type to FintypeCat exists in
  the tree.
* coverMorphism, coverMorphism_over, coverMorphism_bijective: MISSING; they are equivalent to
  Residual 1 below (hom-wise bijections with the actual cover maps).  S1728 proves that the
  target implies such data, so this is a necessary input, not a convenience.
* coverMorphism_id, coverMorphism_comp: MISSING; the coherence part of Residual 1.
* geometricFiberFintype: DERIVED from fiberIdentification by item 5.  For the actual S1726 base
  point this is S1754S1726GeometricFiberFintypeOfIdentification, so no separate finiteness
  input is needed once the fiber functor is identified with the geometric fiber.
* fiberIdentification, fiberIdentification_natural: MISSING; Residual 2, the natural
  identification of the chosen fiber functor with the literal geometric fiber.
* action, isFundamentalGroup: MISSING for the actual arithmetic group, but exactly equivalent to
  Residual 3, one continuous group isomorphism G ≃ₜ* Aut fiber: sufficient by
  S1754S1726ActionAndCertificate, necessary by s1754ContinuousMulEquivOfData.

## Residuals, recorded as types

* S1754S1726StrictRealizationMissing coverCategory: the five categorical fields.
* S1754S1726FiberIdentificationMissing coverCategory fiber: the geometric identification.
* S1754S1726ComparisonMissing fiber: the continuous comparison G ≃ₜ* Aut fiber.

## Honest boundary

No sorry, no admit, no new axiom, no Shrink, ULift, PLift or PUnit, and no fake category, group,
action or fiber functor.  The conditional constructions are real proofs from the stated inputs.
The residuals above are recorded as types; no inhabitant is fabricated.  In particular this file
does NOT construct the S1726 orbicurve fundamental-group datum.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open CategoryTheory
open scoped Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual

universe u v w g

/-! ## 1. Action from a comparison with Aut fiber -/

section Action

variable {C : Type u} [Category.{v} C] (Fib : C ⥤ FintypeCat.{w})

@[implicit_reducible]
noncomputable def s1754ActionOfMonoidHom {G : Type g} [Group G]
    (e : G →* Aut Fib) (Y : C) : MulAction G (Fib.obj Y) :=
  MulAction.compHom (Fib.obj Y) e

theorem s1754ActionOfMonoidHom_smul {G : Type g} [Group G]
    (e : G →* Aut Fib) (Y : C) (gamma : G) (x : Fib.obj Y) :
    letI := s1754ActionOfMonoidHom Fib e Y
    gamma • x = (e gamma).hom.app Y x := rfl

section Certificate

variable [GaloisCategory C] [PreGaloisCategory.FiberFunctor Fib]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem s1754IsFundamentalGroupOfContinuousMulEquiv (e : G ≃ₜ* Aut Fib) :
    letI (Y : C) := s1754ActionOfMonoidHom Fib (e : G →* Aut Fib) Y
    PreGaloisCategory.IsFundamentalGroup Fib G := by
  letI (Y : C) := s1754ActionOfMonoidHom Fib (e : G →* Aut Fib) Y
  exact S1741.isFundamentalGroup_of_continuousMulEquiv (F := Fib) e (fun gamma Y x => rfl)

end Certificate

end Action

/-! ## 2. The three object-level categorical fields -/

structure S1754CoverMapRealization (F : Type u) [Field F]
    (X : Iut.HyperbolicOrbicurve F)
    [Category.{u} (Iut.OrbicurveFiniteEtaleCover X)] where
  map : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
    (source ⟶ target) → source.source.Hom target.source
  overIso : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X}
    (f : source ⟶ target),
    Iso (Pseudofunctor.StrongTrans.vcomp (map f) target.map) source.map
  bijective : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
    Function.Bijective
      (fun f : source ⟶ target =>
        ({ map := map f
           commutes := overIso f } :
          Iut.OrbicurveFiniteEtaleCoverMap source target))

namespace S1754CoverMapRealization

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable [Category.{u} (Iut.OrbicurveFiniteEtaleCover X)]

noncomputable def ofEquiv
    (e : ∀ (A B : Iut.OrbicurveFiniteEtaleCover X),
      (A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B) :
    S1754CoverMapRealization F X where
  map f := (e _ _ f).map
  overIso f := (e _ _ f).commutes
  bijective := by
    intro A B
    have h : (fun f : A ⟶ B =>
        ({ map := (e A B f).map, commutes := (e A B f).commutes } :
          Iut.OrbicurveFiniteEtaleCoverMap A B)) =
        (e A B : (A ⟶ B) → Iut.OrbicurveFiniteEtaleCoverMap A B) := by
      funext f
      cases e A B f
      rfl
    rw [h]
    exact (e A B).bijective

noncomputable def toEquiv
    (r : S1754CoverMapRealization F X) :
    ∀ (A B : Iut.OrbicurveFiniteEtaleCover X),
      (A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B :=
  fun A B =>
    Equiv.ofBijective
      (fun f : A ⟶ B =>
        ({ map := r.map f, commutes := r.overIso f } :
          Iut.OrbicurveFiniteEtaleCoverMap A B))
      (r.bijective (source := A) (target := B))

/-- The three object-level fields of an actual datum are exactly an inhabitant
of S1754CoverMapRealization. -/
noncomputable def ofData {G : ProfiniteGrp.{u}}
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    @S1754CoverMapRealization F _ X D.coverCategory := by
  letI := D.coverCategory
  exact
    { map := D.coverMorphism
      overIso := D.coverMorphism_over
      bijective := D.coverMorphism_bijective }

theorem nonempty_iff :
    Nonempty (S1754CoverMapRealization F X) ↔
      ∀ (A B : Iut.OrbicurveFiniteEtaleCover X),
        Nonempty ((A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B) := by
  constructor
  · rintro ⟨r⟩ A B
    exact ⟨r.toEquiv A B⟩
  · intro h
    exact ⟨S1754CoverMapRealization.ofEquiv (fun A B => Classical.choice (h A B))⟩

end S1754CoverMapRealization

/-! ## 3. The five categorical fields -/

structure S1754StrictCoverMapRealization (F : Type u) [Field F]
    (X : Iut.HyperbolicOrbicurve F)
    [Category.{u} (Iut.OrbicurveFiniteEtaleCover X)] where
  map : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
    (source ⟶ target) → source.source.Hom target.source
  overIso : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X}
    (f : source ⟶ target),
    Iso (Pseudofunctor.StrongTrans.vcomp (map f) target.map) source.map
  bijective : ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
    Function.Bijective
      (fun f : source ⟶ target =>
        ({ map := map f
           commutes := overIso f } :
          Iut.OrbicurveFiniteEtaleCoverMap source target))
  id_iso : ∀ (cover : Iut.OrbicurveFiniteEtaleCover X),
    Iso (map (𝟙 cover)) (Pseudofunctor.StrongTrans.id cover.source.fiber)
  comp_iso : ∀ {first second third : Iut.OrbicurveFiniteEtaleCover X}
      (f : first ⟶ second) (g : second ⟶ third),
    Iso (map (f ≫ g))
      (Pseudofunctor.StrongTrans.vcomp (map f) (map g))

namespace S1754StrictCoverMapRealization

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

noncomputable def ofData
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    @S1754StrictCoverMapRealization F _ X D.coverCategory := by
  letI := D.coverCategory
  exact
    { map := D.coverMorphism
      overIso := D.coverMorphism_over
      bijective := D.coverMorphism_bijective
      id_iso := D.coverMorphism_id
      comp_iso := D.coverMorphism_comp }

theorem nonempty_of_data
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    Nonempty (@S1754StrictCoverMapRealization F _ X D.coverCategory) :=
  ⟨ofData D⟩

end S1754StrictCoverMapRealization


/-! ## 3b. The exact residual, stated as hom-wise equivalences with the cover
maps, compatible with identity and composition -/

section StrictHomEquiv

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable [Category.{u} (Iut.OrbicurveFiniteEtaleCover X)]

/-- Hom-wise equivalences between the categorical homs and the actual cover
maps, strictly compatible with identities and composition up to
2-isomorphism.  This is the residual input needed for the five categorical
fields. -/
structure S1754StrictHomEquiv where
  equiv : ∀ (A B : Iut.OrbicurveFiniteEtaleCover X),
    (A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B
  id_compat : ∀ (cover : Iut.OrbicurveFiniteEtaleCover X),
    Iso ((equiv cover cover (𝟙 cover)).map)
      (Pseudofunctor.StrongTrans.id cover.source.fiber)
  comp_compat : ∀ {first second third : Iut.OrbicurveFiniteEtaleCover X}
      (f : first ⟶ second) (g : second ⟶ third),
    Iso ((equiv first third (f ≫ g)).map)
      (Pseudofunctor.StrongTrans.vcomp
        (equiv first second f).map (equiv second third g).map)

namespace S1754StrictHomEquiv

/-- The five fields give the strict hom-wise equivalences. -/
noncomputable def ofRealization
    (r : S1754StrictCoverMapRealization F X) :
    S1754StrictHomEquiv (F := F) (X := X) where
  equiv := fun A B =>
    Equiv.ofBijective
      (fun f : A ⟶ B =>
        ({ map := r.map f, commutes := r.overIso f } :
          Iut.OrbicurveFiniteEtaleCoverMap A B))
      (r.bijective (source := A) (target := B))
  id_compat := fun cover => r.id_iso cover
  comp_compat := fun f g => r.comp_iso f g

/-- The strict hom-wise equivalences give the five fields. -/
noncomputable def toRealization
    (s : S1754StrictHomEquiv (F := F) (X := X)) :
    S1754StrictCoverMapRealization F X where
  map f := (s.equiv _ _ f).map
  overIso f := (s.equiv _ _ f).commutes
  bijective := by
    intro A B
    have h : (fun f : A ⟶ B =>
        ({ map := (s.equiv A B f).map,
           commutes := (s.equiv A B f).commutes } :
          Iut.OrbicurveFiniteEtaleCoverMap A B)) =
        (s.equiv A B :
          (A ⟶ B) → Iut.OrbicurveFiniteEtaleCoverMap A B) := by
      funext f
      cases s.equiv A B f
      rfl
    rw [h]
    exact (s.equiv A B).bijective
  id_iso := fun cover => s.id_compat cover
  comp_iso := fun f g => s.comp_compat f g

/-- The five categorical fields exist if and only if the hom types admit
equivalences with the actual cover maps that are compatible with identities
and composition. -/
theorem nonempty_iff :
    Nonempty (S1754StrictCoverMapRealization F X) ↔
      Nonempty (S1754StrictHomEquiv (F := F) (X := X)) := by
  constructor
  · rintro ⟨r⟩
    exact ⟨ofRealization r⟩
  · rintro ⟨s⟩
    exact ⟨toRealization s⟩

end S1754StrictHomEquiv

end StrictHomEquiv

/-! ## 4. Geometric finiteness is a consequence of the fiber identification -/

section GeometricFiber

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable [Category.{u} (Iut.OrbicurveFiniteEtaleCover X)]

@[implicit_reducible]
noncomputable def s1754GeometricFiberFintypeOfIdentification
    (baseScheme : Iut.SchemeOverField F)
    (basePoint : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (fiber : Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u})
    (ident : ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      (fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber baseScheme basePoint cover) :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      Fintype (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        baseScheme basePoint cover) :=
  fun cover =>
    letI : Fintype ((fiber.obj cover).obj) := FintypeCat.fintype
    Fintype.ofEquiv ((fiber.obj cover).obj) (ident cover)

variable {G : ProfiniteGrp.{u}}

@[implicit_reducible]
noncomputable def s1754GeometricFiberFintypeOfData
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      Fintype (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        D.baseScheme D.basePoint cover) := by
  letI := D.coverCategory
  exact s1754GeometricFiberFintypeOfIdentification
    D.baseScheme D.basePoint D.fiber D.fiberIdentification

end GeometricFiber

/-! ## 4b. Conversely, every datum yields the continuous comparison -/

section ComparisonOfData

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

/-- Every actual datum supplies exactly the fiber identification family: the
fiberIdentification field is itself the residual datum, with D's own base
fields. -/
noncomputable def s1754FiberIdentificationOfData
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    letI := D.coverCategory
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      (D.fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          D.baseScheme D.basePoint cover := by
  letI := D.coverCategory
  exact fun cover => D.fiberIdentification cover

/-- Every actual datum yields a continuous group isomorphism between the stored
group and the automorphism group of the stored fiber functor.  Hence the group
comparison of Residual 3 is not extra structure: it is canonically determined
by the datum, and together with the action construction of section 1 it is
equivalent to the two group-theoretic fields. -/
noncomputable def s1754ContinuousMulEquivOfData
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    (G : Type u) ≃ₜ* Aut D.fiber := by
  letI := D.coverCategory
  letI := D.galoisCategory
  letI := D.fiberFunctor
  letI (cover : Iut.OrbicurveFiniteEtaleCover X) := D.action cover
  letI := D.isFundamentalGroup
  exact
    ContinuousMulEquiv.mk' (PreGaloisCategory.toAutHomeo D.fiber (G : Type u))
      (fun x y =>
        map_mul (PreGaloisCategory.toAutMulEquiv D.fiber (G : Type u)) x y)

end ComparisonOfData


/-! ## 5. The reduced field list: the datum is constructible from these pieces -/

structure S1754Pieces (F : Type u) [Field F]
    (X : Iut.HyperbolicOrbicurve F) (G : ProfiniteGrp.{u}) where
  coverCategory : Category.{u} (Iut.OrbicurveFiniteEtaleCover X)
  galoisCategory :
    letI := coverCategory
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) coverCategory
  baseScheme : Iut.SchemeOverField F
  basePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber
  fiber :
    letI := coverCategory
    Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  real :
    letI := coverCategory
    S1754StrictCoverMapRealization F X
  fiberIdentification :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      (fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover
  fiberIdentification_natural :
    letI := coverCategory
    ∀ {source target : Iut.OrbicurveFiniteEtaleCover X}
      (map : source ⟶ target) (element : (fiber.obj source).obj),
      fiberIdentification target (fiber.map map element) =
        (Iut.OrbicurveFiniteEtaleCover.geometricFiberMap
          (real.map map) (real.overIso map)
          baseScheme basePoint).obj
            (fiberIdentification source element)
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      MulAction G (fiber.obj cover)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (cover : Iut.OrbicurveFiniteEtaleCover X) := action cover
    PreGaloisCategory.IsFundamentalGroup fiber G

namespace S1754Pieces

variable {F : Type u} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

noncomputable def toDatum (P : S1754Pieces F X G) :
    Iut.OrbicurveEtaleFundamentalGroup X G := by
  letI := P.coverCategory
  letI := P.galoisCategory
  letI := P.fiberFunctor
  letI (cover : Iut.OrbicurveFiniteEtaleCover X) := P.action cover
  exact
    { coverCategory := P.coverCategory
      galoisCategory := P.galoisCategory
      baseScheme := P.baseScheme
      basePoint := P.basePoint
      fiber := P.fiber
      fiberFunctor := P.fiberFunctor
      coverMorphism := P.real.map
      coverMorphism_over := P.real.overIso
      coverMorphism_bijective := P.real.bijective
      coverMorphism_id := P.real.id_iso
      coverMorphism_comp := P.real.comp_iso
      geometricFiberFintype :=
        s1754GeometricFiberFintypeOfIdentification
          P.baseScheme P.basePoint P.fiber P.fiberIdentification
      fiberIdentification := P.fiberIdentification
      fiberIdentification_natural := P.fiberIdentification_natural
      action := P.action
      isFundamentalGroup := P.isFundamentalGroup }

noncomputable def ofData (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    S1754Pieces F X G := by
  letI := D.coverCategory
  exact
    { coverCategory := D.coverCategory
      galoisCategory := D.galoisCategory
      baseScheme := D.baseScheme
      basePoint := D.basePoint
      fiber := D.fiber
      fiberFunctor := D.fiberFunctor
      real := S1754StrictCoverMapRealization.ofData D
      fiberIdentification := D.fiberIdentification
      fiberIdentification_natural := D.fiberIdentification_natural
      action := D.action
      isFundamentalGroup := D.isFundamentalGroup }

theorem nonempty (P : S1754Pieces F X G) :
    Nonempty (Iut.OrbicurveEtaleFundamentalGroup X G) :=
  ⟨P.toDatum⟩

/-- Each piece list supplies S1728's small raw cover-map data with the
categorical hom type as the small carrier. -/
noncomputable def smallRawCoverData (P : S1754Pieces F X G)
    (A B : Iut.OrbicurveFiniteEtaleCover X) :
    LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728SmallRawCoverData
      (F := F) (X := X) A B := by
  letI := P.coverCategory
  exact
    { Carrier := (A ⟶ B)
      equiv := Equiv.ofBijective
        (fun f : A ⟶ B =>
          ({ map := P.real.map f, commutes := P.real.overIso f } :
            Iut.OrbicurveFiniteEtaleCoverMap A B))
        (P.real.bijective (source := A) (target := B)) }

/-- The target datum is inhabited if and only if the reduced piece list is
inhabited.  The only field of the target that is not an independent input is
geometricFiberFintype, which is derived from fiberIdentification. -/
theorem nonempty_iff :
    Nonempty (S1754Pieces F X G) ↔
      Nonempty (Iut.OrbicurveEtaleFundamentalGroup X G) := by
  constructor
  · rintro ⟨P⟩
    exact P.nonempty
  · rintro ⟨D⟩
    exact ⟨ofData D⟩

end S1754Pieces


/-! ## 6. The S1726 instance: the actual cover type and the exact residuals -/

section S1726

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-- The actual S1726 cover type: a Type 1 type. -/
abbrev S1754S1726Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S1726Orbicurve

/-- The target datum for the actual S1726 orbicurve. -/
abbrev S1754S1726Target (G : ProfiniteGrp.{0}) : Type 1 :=
  Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G

/-- The actual S1726 cover-map type: Type 1. -/
abbrev S1754S1726CoverMap (A B : S1754S1726Cover) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- The S1726 base scheme, the affine model Spec R' over Spec F'. -/
abbrev S1754S1726BaseScheme : Iut.SchemeOverField S1726K :=
  S1726AffineOver

/-- The actual S1726 base point: the identity strong transformation of the
representable pseudofunctor. -/
noncomputable def S1754S1726BasePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor S1726K S1754S1726BaseScheme)
      S1726Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- **Residual 1 (the five categorical fields).**  For a small category
structure on the actual S1726 cover type, the five categorical fields are
equivalent to hom-wise equivalences with the actual cover maps that are
compatible with identities and composition. -/
def S1754S1726StrictRealizationMissing
    (coverCategory : Category.{0} S1754S1726Cover) : Prop :=
  letI := coverCategory
  Nonempty (S1754StrictHomEquiv (F := S1726K) (X := S1726Orbicurve))

/-- Every actual S1726 datum supplies residual 1, i.e. the five categorical
fields are exactly this residual. -/
theorem S1754S1726StrictRealizationMissing_of_data
    {G : ProfiniteGrp.{0}} (D : S1754S1726Target G) :
    S1754S1726StrictRealizationMissing D.coverCategory := by
  letI := D.coverCategory
  exact ⟨S1754StrictHomEquiv.ofRealization
    (S1754StrictCoverMapRealization.ofData D)⟩

/-- **Residual 2 (the geometric fiber identification).**  For the actual S1726
base point, an equivalence of the chosen fiber functor with the literal
geometric fiber, natural in the categorical variable. -/
def S1754S1726FiberIdentificationMissing
    (coverCategory : Category.{0} S1754S1726Cover)
    (fiber : letI := coverCategory; S1754S1726Cover ⥤ FintypeCat.{0}) : Type 1 :=
  letI := coverCategory
  ∀ cover : S1754S1726Cover,
    (fiber.obj cover).obj ≃
      Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        S1754S1726BaseScheme S1754S1726BasePoint cover

/-- **Residual 2 implies the geometric finiteness field.**  The literal
geometric fiber of every S1726 cover is finite as soon as the fiber functor is
identified with it. -/
@[implicit_reducible]
noncomputable def S1754S1726GeometricFiberFintypeOfIdentification
    (coverCategory : Category.{0} S1754S1726Cover)
    (fiber : letI := coverCategory; S1754S1726Cover ⥤ FintypeCat.{0})
    (ident : S1754S1726FiberIdentificationMissing coverCategory fiber) :
    ∀ cover : S1754S1726Cover,
      Fintype (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        S1754S1726BaseScheme S1754S1726BasePoint cover) := by
  letI := coverCategory
  exact s1754GeometricFiberFintypeOfIdentification
    S1754S1726BaseScheme S1754S1726BasePoint fiber ident

end S1726

section S1726Action

variable [Category.{0} S1754S1726Cover]
variable [GaloisCategory S1754S1726Cover]
variable (fiber : S1754S1726Cover ⥤ FintypeCat.{0})
variable [PreGaloisCategory.FiberFunctor fiber]
variable {G : ProfiniteGrp.{0}}

/-- **Residual 3 (the group action and the fundamental-group certificate).**
A continuous group isomorphism between the arithmetic group and the
automorphism group of the fiber functor. -/
abbrev S1754S1726ComparisonMissing : Type 1 :=
  (G : Type) ≃ₜ* Aut fiber

/-- From residual 3 both the action field and the isFundamentalGroup field are
constructed: the action is the transport of the tautological Aut-action, and
the certificate is S1741's transport theorem. -/
theorem S1754S1726ActionAndCertificate
    (e : S1754S1726ComparisonMissing (G := G) (fiber := fiber)) :
    letI (cover : S1754S1726Cover) :=
      s1754ActionOfMonoidHom fiber (e.toMulEquiv.toMonoidHom) cover
    PreGaloisCategory.IsFundamentalGroup fiber (G : Type) := by
  letI (cover : S1754S1726Cover) :=
    s1754ActionOfMonoidHom fiber (e.toMulEquiv.toMonoidHom) cover
  exact s1754IsFundamentalGroupOfContinuousMulEquiv fiber e

end S1726Action

/-! ## 7. Axiom footprint -/

#check @S1754CoverMapRealization.nonempty_iff
#check @S1754StrictHomEquiv.nonempty_iff
#check @s1754GeometricFiberFintypeOfIdentification
#check @s1754GeometricFiberFintypeOfData
#check @s1754IsFundamentalGroupOfContinuousMulEquiv
#check @S1754Pieces.toDatum
#check @S1754Pieces.ofData
#check @S1754CoverMapRealization.ofData
#check @S1754Pieces.nonempty_iff
#check @s1754FiberIdentificationOfData
#check @s1754ContinuousMulEquivOfData
#check @S1754Pieces.smallRawCoverData
#check @S1754S1726ActionAndCertificate
#check @S1754S1726StrictRealizationMissing_of_data

#print axioms S1754CoverMapRealization.nonempty_iff
#print axioms S1754StrictHomEquiv.nonempty_iff
#print axioms s1754GeometricFiberFintypeOfIdentification
#print axioms s1754GeometricFiberFintypeOfData
#print axioms s1754IsFundamentalGroupOfContinuousMulEquiv
#print axioms S1754Pieces.toDatum
#print axioms S1754Pieces.ofData
#print axioms s1754FiberIdentificationOfData
#print axioms s1754ContinuousMulEquivOfData
#print axioms S1754Pieces.smallRawCoverData
#print axioms S1754CoverMapRealization.ofData
#print axioms S1754Pieces.nonempty_iff
#print axioms S1754S1726StrictRealizationMissing_of_data

end LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual
