/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1735GeometricFiberActual
import tmp.sheaf.xif.paper.S1754OrbicurvePiFieldsActual

/-!
# S1788: the R2 natural identification with the literal geometric fiber at
`S1726AffineOver` / identity

## Target

S1754 records the residual

  `S1754S1726FiberIdentificationMissing coverCategory fiber`
    = for every cover, `(fiber.obj cover).obj ≃ GeometricFiber S1726AffineOver id cover`,

together with the naturality field of `OrbicurveEtaleFundamentalGroup`.  The
present file attacks exactly that residual at the actual S1726 base point

  baseScheme = S1726AffineOver,
  basePoint  = the identity strong transformation.

## What is constructed

* The actual base point `S1788BasePoint` at `S1726AffineOver`/identity, proved
  definitionally equal to `S1754S1726BasePoint`.

* For a `Category.{0,1}` structure on the actual cover type and a
  `StrictCoverData` datum at that point, the canonical geometric fiber functor
  `S1788FiberFunctor`, whose objects are the literal geometric fibers and
  whose maps are the literal geometric-fiber maps.

* The R2 identification

    `S1788FiberIdentification D :
       ∀ cover, ((S1788FiberFunctor D).obj cover).obj ≃ S1788Fiber cover`

  and the exact statement `S1788R2 D` of type
  `S1754S1726FiberIdentificationMissing`.  The identification is the identity
  equivalence; it is not an extra geometric datum because the canonical
  functor's object type is *definitionally* the literal geometric fiber.

* The naturality theorem `S1788FiberIdentification_natural`, with the exact
  S1754 naturality shape.  It is `rfl` after unfolding the functor's map: the
  canonical functor's map is by definition `geomFiberMap` of the chosen strict
  cover datum.

* The packaged datum `S1788FiberIdentificationData` (S1735's
  `FiberIdentificationData`: a fiber functor, pointwise equivalences with the
  literal geometric fibers, and their naturality).

* The bundled natural isomorphism `S1788FiberNatIso`: from any fiber
  identification datum, a genuine natural isomorphism in `FintypeCat` between
  its fiber functor and the canonical geometric fiber functor.

## Exact content of R2

The key exact statement is

  `S1788FiberIdentificationData_nonempty_iff`:
    `Nonempty (FiberIdentificationData ...) ↔
       Nonempty (StrictCoverData ...)`

for a fixed cover category, and the existence-level form
`S1788FiberIdentificationExists_iff`.  Thus, at the actual S1726 base point,
the existence of *some* fiber functor together with a natural identification
with the literal geometric fiber is exactly the existence of the strict cover
datum.  The natural identification is not an independent geometric
obstruction; the strict datum is the exact missing input.

## Exact missing (no fake)

The actual cover type is a `Type 1` type.  S1728 constructs a
`Category.{0,1}` on it only conditionally on small raw cover-map data, and no
such unconditional category is supplied by S1735/S1754.  Consequently the
canonical functor and R2 are conditional on exactly:

1. a `Category.{0,1}` on `OrbicurveFiniteEtaleCover S1726Orbicurve`;
2. `StrictCoverData` at `S1726AffineOver`/identity, whose fields are:
   * a realization `coverMorphism` / `coverMorphism_over` of the categorical
     homs by actual cover maps,
   * `Fintype` (or `Finite`) on every literal geometric fiber (the parallel
     S1780 finiteness task),
   * the strict identity and composition laws for the literal geometric-fiber
     maps (S1764 records that these are not consequences of the raw
     pseudofunctor).

The file also records the decomposition `S1788StrictCoverDataOfParts`: a
cover-map realization, a finiteness proposition, and the two strict laws
suffice.  No category, fiber, finiteness instance or strict law is faked.  No
`sorry`, `admit` or new axiom is used.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms`
block at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1788FiberIdentificationActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual

/-! ## 1. The actual base data: `S1726AffineOver` / identity -/

/-- The actual base field `F'` of S1726. -/
abbrev S1788K : Type := S1726K

/-- The actual D6 orbicurve `X = S1726Orbicurve` over `F'`. -/
abbrev S1788Orbicurve : HyperbolicOrbicurve S1788K := S1726Orbicurve

/-- The actual base scheme: the affine model `S1726AffineOver = Spec R'`. -/
abbrev S1788BaseScheme : SchemeOverField S1788K := S1726AffineOver

/-- The actual base point `S1726AffineOver`/identity: the identity strong
transformation.  The stack fiber of `S1726Orbicurve` is definitionally the
representable pseudofunctor of `S1726AffineOver`, so this is a genuine
scheme-valued point. -/
noncomputable def S1788BasePoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1788K S1788BaseScheme)
      S1788Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- The actual cover type of `S1726Orbicurve`. -/
abbrev S1788Cover : Type 1 := OrbicurveFiniteEtaleCover S1788Orbicurve

/-- The literal geometric fiber at the actual `S1726AffineOver`/identity
point.  This is the object type appearing on the right of R2. -/
abbrev S1788Fiber (cover : S1788Cover) : Type :=
  GeomFiber (F := S1788K) (X := S1788Orbicurve)
    S1788BaseScheme S1788BasePoint cover

/-- The actual base point is exactly `S1754S1726BasePoint`. -/
theorem S1788BasePoint_eq : S1788BasePoint = S1754S1726BasePoint := rfl

/-- The actual base scheme is exactly `S1754S1726BaseScheme`. -/
theorem S1788BaseScheme_eq : S1788BaseScheme = S1754S1726BaseScheme := rfl

/-- The actual cover type is exactly `S1754S1726Cover`. -/
theorem S1788Cover_eq : S1788Cover = S1754S1726Cover := rfl

/-! ## 2. The canonical geometric fiber functor -/

section Canonical

variable [Category.{0, 1} S1788Cover]

variable (D : StrictCoverData (F := S1788K) (X := S1788Orbicurve)
  S1788BaseScheme S1788BasePoint)

/-- The canonical geometric fiber functor at the actual
`S1726AffineOver`/identity point: its objects are the literal geometric
fibers and its maps are the literal geometric-fiber maps.  This is S1735's
`geometricFiberFunctor`, specialized to the actual S1726 data.  It is
conditional exactly on the `Category.{0,1}` structure and `StrictCoverData`. -/
noncomputable abbrev S1788FiberFunctor : S1788Cover ⥤ FintypeCat.{0} :=
  geometricFiberFunctor (F := S1788K) (X := S1788Orbicurve)
    S1788BaseScheme S1788BasePoint D

/-- The object of the canonical functor is exactly the finite-type package of
the literal geometric fiber. -/
@[simp] theorem S1788FiberFunctor_obj (cover : S1788Cover) :
    (S1788FiberFunctor D).obj cover =
      fiberFintypeCat (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint D cover := rfl

/-- The underlying type of the canonical functor's object is literally the
geometric fiber.  This is the definitional equality that makes R2 the identity
identification. -/
@[simp] theorem S1788FiberFunctor_obj_obj (cover : S1788Cover) :
    ((S1788FiberFunctor D).obj cover).obj = S1788Fiber cover := rfl

/-- On a categorical arrow the canonical functor's map is exactly the literal
geometric-fiber map of the strict cover realization. -/
theorem S1788FiberFunctor_map_apply {A B : S1788Cover} (f : A ⟶ B)
    (x : S1788Fiber A) :
    (S1788FiberFunctor D).map f x =
      geomFiberMap (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B) x :=
  geometricFiberFunctor_map_apply (F := S1788K) (X := S1788Orbicurve)
    S1788BaseScheme S1788BasePoint D f x

/-! ## 3. The R2 identification and its naturality -/

/-- The R2 identification: at every cover, the object of the canonical
geometric fiber functor is equivalent to the literal geometric fiber.  This is
the identity equivalence, made possible by the definitional equality
`S1788FiberFunctor_obj_obj`; it is not a choice of extra data. -/
noncomputable abbrev S1788FiberIdentification :
    ∀ cover : S1788Cover,
      ((S1788FiberFunctor D).obj cover).obj ≃ S1788Fiber cover :=
  fun cover => Equiv.refl _

/-- The exact S1754 residual: the object-level fiber identification for the
canonical geometric fiber functor. -/
noncomputable def S1788R2 :
    S1754S1726FiberIdentificationMissing
      ‹Category.{0, 1} S1788Cover› (S1788FiberFunctor D) :=
  S1788FiberIdentification D

/-- The R2 identification is the identity on elements. -/
@[simp] theorem S1788FiberIdentification_apply (cover : S1788Cover)
    (x : ((S1788FiberFunctor D).obj cover).obj) :
    S1788FiberIdentification D cover x = x := rfl

/-- Naturality of the R2 identification, in the exact S1754 shape: the
canonical functor's map commutes with the identification and the literal
geometric-fiber map.  The proof is `rfl` after unfolding the canonical
functor's map; no geometric input beyond the strict cover datum is used. -/
theorem S1788FiberIdentification_natural {A B : S1788Cover} (f : A ⟶ B)
    (x : ((S1788FiberFunctor D).obj A).obj) :
    S1788FiberIdentification D B ((S1788FiberFunctor D).map f x) =
      (OrbicurveFiniteEtaleCover.geometricFiberMap
        (D.coverMorphism f) (D.coverMorphism_over f)
        S1788BaseScheme S1788BasePoint).obj
        (S1788FiberIdentification D A x) := by
  change (ConcreteCategory.hom
      ((geometricFiberFunctor (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint D).map f)) x =
    (OrbicurveFiniteEtaleCover.geometricFiberMap
      (D.coverMorphism f) (D.coverMorphism_over f)
      S1788BaseScheme S1788BasePoint).obj x
  rw [geometricFiberFunctor_map_apply]
  rfl

/-- The naturality statement in the bundled form used by S1735's
`FiberIdentificationData` and by `OrbicurveEtaleFundamentalGroup`. -/
theorem S1788FiberIdentification_natural_bundled {A B : S1788Cover}
    (f : A ⟶ B) (x : ((S1788FiberFunctor D).obj A).obj) :
    S1788FiberIdentification D B ((S1788FiberFunctor D).map f x) =
      geomFiberMap (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B)
        (S1788FiberIdentification D A x) := by
  exact S1788FiberIdentification_natural D f x

/-! ## 4. The packaged fiber-identification datum -/

/-- The complete fiber-identification datum at the actual
`S1726AffineOver`/identity point: a fiber functor, pointwise equivalences with
the literal geometric fibers, their naturality, and the actual-cover-map
realization.  This is exactly S1754's R2 plus the naturality field, packaged. -/
noncomputable def S1788FiberIdentificationData :
    FiberIdentificationData (F := S1788K) (X := S1788Orbicurve)
      S1788BaseScheme S1788BasePoint where
  coverMorphism := D.coverMorphism
  coverMorphism_over := D.coverMorphism_over
  fiber := S1788FiberFunctor D
  fiberIdentification := fun cover => Equiv.refl _
  fiberIdentification_natural := by
    intro A B f x
    exact S1788FiberIdentification_natural D f x

/-- The packaged datum really has the canonical fiber functor. -/
@[simp] theorem S1788FiberIdentificationData_fiber :
    (S1788FiberIdentificationData D).fiber = S1788FiberFunctor D := rfl

/-- The packaged datum really has the R2 identification. -/
@[simp] theorem S1788FiberIdentificationData_identification (cover : S1788Cover) :
    (S1788FiberIdentificationData D).fiberIdentification cover =
      (Equiv.refl _ : ((S1788FiberFunctor D).obj cover).obj ≃ S1788Fiber cover) :=
  rfl

end Canonical

/-! ## 5. The bundled natural isomorphism with the canonical functor -/

section NaturalIso

variable [Category.{0, 1} S1788Cover]

variable (E : FiberIdentificationData (F := S1788K) (X := S1788Orbicurve)
  S1788BaseScheme S1788BasePoint)

/-- The canonical geometric fiber functor obtained from a fiber-identification
datum by S1735's strictification theorem. -/
noncomputable abbrev S1788FiberFunctorOfData : S1788Cover ⥤ FintypeCat.{0} :=
  S1788FiberFunctor (strictCoverDataOfFiberIdentification E)

/-- The components of the natural isomorphism: the fiber identification
itself, viewed as an isomorphism in `FintypeCat`. -/
noncomputable def S1788FiberNatIsoComponent (cover : S1788Cover) :
    E.fiber.obj cover ≅ (S1788FiberFunctorOfData E).obj cover where
  hom := FintypeCat.homMk
    (show (E.fiber.obj cover).obj →
        ((S1788FiberFunctorOfData E).obj cover).obj
      from E.fiberIdentification cover)
  inv := FintypeCat.homMk
    (show ((S1788FiberFunctorOfData E).obj cover).obj →
        (E.fiber.obj cover).obj
      from (E.fiberIdentification cover).symm)
  hom_inv_id := by
    apply FintypeCat.hom_ext
    intro x
    change (E.fiberIdentification cover).symm
        ((E.fiberIdentification cover) x) = x
    exact Equiv.symm_apply_apply _ x
  inv_hom_id := by
    apply FintypeCat.hom_ext
    intro x
    change (E.fiberIdentification cover)
        ((E.fiberIdentification cover).symm x) = x
    exact Equiv.apply_symm_apply _ x

/-- R2, its naturality, and S1735's strictification, bundled as one natural
isomorphism between the chosen fiber functor and the canonical geometric
fiber functor.  This is the functor-level form of the R2 identification. -/
noncomputable def S1788FiberNatIso : E.fiber ≅ S1788FiberFunctorOfData E :=
  NatIso.ofComponents (fun cover => S1788FiberNatIsoComponent E cover)
    (by
      intro A B f
      apply FintypeCat.hom_ext
      intro x
      change (FintypeCat.homMk
          (show (E.fiber.obj B).obj →
              ((S1788FiberFunctorOfData E).obj B).obj
            from E.fiberIdentification B)) (E.fiber.map f x) =
        (S1788FiberFunctorOfData E).map f
          ((FintypeCat.homMk
            (show (E.fiber.obj A).obj →
                ((S1788FiberFunctorOfData E).obj A).obj
              from E.fiberIdentification A)) x)
      simp only [FintypeCat.homMk_apply]
      rw [E.fiberIdentification_natural f x]
      change (OrbicurveFiniteEtaleCover.geometricFiberMap
          (E.coverMorphism f) (E.coverMorphism_over f)
          S1788BaseScheme S1788BasePoint).obj
          (E.fiberIdentification A x) =
        (ConcreteCategory.hom
          ((geometricFiberFunctor (F := S1788K) (X := S1788Orbicurve)
            S1788BaseScheme S1788BasePoint
            (strictCoverDataOfFiberIdentification E)).map f))
          (E.fiberIdentification A x)
      rw [geometricFiberFunctor_map_apply]
      rfl)

/-- The natural isomorphism is the fiber identification on elements. -/
@[simp] theorem S1788FiberNatIso_hom_app (cover : S1788Cover)
    (x : (E.fiber.obj cover).obj) :
    (S1788FiberNatIso E).hom.app cover x =
      E.fiberIdentification cover x := rfl

end NaturalIso

/-! ## 6. R2 plus naturality is exactly the strict cover datum -/

section Exactness

variable [Category.{0, 1} S1788Cover]

/-- For a fixed cover category, the existence of a fiber functor together with
a natural identification with the literal geometric fiber is exactly the
existence of the strict cover datum.  The forward direction is S1735's
`strictCoverDataOfFiberIdentification`; the converse uses the canonical
geometric fiber functor and the identity identification. -/
theorem S1788FiberIdentificationData_nonempty_iff :
    Nonempty (FiberIdentificationData (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint) ↔
      Nonempty (StrictCoverData (F := S1788K) (X := S1788Orbicurve)
        S1788BaseScheme S1788BasePoint) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨strictCoverDataOfFiberIdentification E⟩
  · rintro ⟨D⟩
    exact ⟨S1788FiberIdentificationData D⟩

/-- Any fiber-identification datum directly supplies the object-level R2
family for its own fiber functor. -/
theorem S1788R2_of_fiberIdentificationData
    (E : FiberIdentificationData (F := S1788K) (X := S1788Orbicurve)
      S1788BaseScheme S1788BasePoint) :
    Nonempty (@S1754S1726FiberIdentificationMissing
      ‹Category.{0, 1} S1788Cover› E.fiber) :=
  ⟨E.fiberIdentification⟩

end Exactness

/-! ## 7. The exact missing input at the actual S1726 point -/

/-- The exact missing input for the R2 natural identification at
`S1726AffineOver`/identity: a `Category.{0,1}` on the actual cover type
together with `StrictCoverData`.  Neither component is supplied by
S1735/S1754: the category is S1728's first missing small-cover input, and the
strict datum contains the geometric-fiber finiteness (S1780) and the strict
identity and composition laws (S1764). -/
def S1788CategoryAndStrictDataRequired : Prop :=
  ∃ C : Category.{0, 1} S1788Cover,
    letI := C
    Nonempty (StrictCoverData (F := S1788K) (X := S1788Orbicurve)
      S1788BaseScheme S1788BasePoint)

/-- The existence of a natural fiber identification at the actual S1726
point: some cover category and some fiber functor with a natural
identification to the literal geometric fibers. -/
def S1788FiberIdentificationExists : Prop :=
  ∃ C : Category.{0, 1} S1788Cover,
    letI := C
    Nonempty (FiberIdentificationData (F := S1788K) (X := S1788Orbicurve)
      S1788BaseScheme S1788BasePoint)

/-- The existence of a natural fiber identification is exactly the exact
missing input. -/
theorem S1788FiberIdentificationExists_iff :
    S1788FiberIdentificationExists ↔ S1788CategoryAndStrictDataRequired := by
  constructor
  · rintro ⟨C, h⟩
    letI := C
    rcases h with ⟨E⟩
    exact ⟨C, ⟨strictCoverDataOfFiberIdentification E⟩⟩
  · rintro ⟨C, h⟩
    letI := C
    rcases h with ⟨D⟩
    exact ⟨C, ⟨S1788FiberIdentificationData D⟩⟩

/-- The literal R2 residual exists whenever the exact missing input is
supplied.  The witness is the canonical geometric fiber functor and the
identity identification. -/
theorem S1788R2_exists_of_exactMissing
    (h : S1788CategoryAndStrictDataRequired) :
    ∃ (C : Category.{0, 1} S1788Cover)
      (fiber : letI := C; S1788Cover ⥤ FintypeCat.{0}),
      letI := C
      Nonempty (@S1754S1726FiberIdentificationMissing C fiber) := by
  rcases h with ⟨C, hD⟩
  letI := C
  rcases hD with ⟨D⟩
  exact ⟨C, S1788FiberFunctor D, ⟨S1788FiberIdentification D⟩⟩

/-! ## 8. Decomposition of the exact missing input

The strict datum splits into a cover-map realization, the geometric-fiber
finiteness proposition, and the two strict functor laws.  This records
exactly which part is attacked by the S1780 finiteness task and which part is
the strictification obstruction of S1764. -/

section Decomposition

variable [Category.{0, 1} S1788Cover]

/-- The literal geometric-fiber finiteness input at the actual
`S1726AffineOver`/identity point.  This is the S1780 target, recorded as a
`Prop`; it is not asserted here. -/
def S1788FiberFiniteRequired : Prop :=
  ∀ cover : S1788Cover, Nonempty (Fintype (S1788Fiber cover))

/-- The two strict functor laws for a chosen realization of the categorical
homs by actual cover maps.  These are exactly the `map_id` and `map_comp`
fields of `StrictCoverData`; S1764 records that the raw pseudofunctor only
supplies natural isomorphisms, not these equalities. -/
structure S1788StrictFiberLaws
    (coverMorphism : ∀ {A B : S1788Cover},
      (A ⟶ B) → A.source.Hom B.source)
    (coverMorphism_over : ∀ {A B : S1788Cover} (f : A ⟶ B),
      Iso (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map) A.map) :
    Prop where
  map_id : ∀ cover : S1788Cover,
    (OrbicurveFiniteEtaleCover.geometricFiberMap
        (coverMorphism (𝟙 cover)) (coverMorphism_over (𝟙 cover))
        S1788BaseScheme S1788BasePoint).obj = id
  map_comp : ∀ {A B C : S1788Cover} (f : A ⟶ B) (g : B ⟶ C),
    (fun x =>
      (OrbicurveFiniteEtaleCover.geometricFiberMap
        (coverMorphism (f ≫ g)) (coverMorphism_over (f ≫ g))
        S1788BaseScheme S1788BasePoint).obj x) =
      (fun x =>
        (OrbicurveFiniteEtaleCover.geometricFiberMap
          (coverMorphism g) (coverMorphism_over g)
          S1788BaseScheme S1788BasePoint).obj
          ((OrbicurveFiniteEtaleCover.geometricFiberMap
            (coverMorphism f) (coverMorphism_over f)
            S1788BaseScheme S1788BasePoint).obj x))

/-- The strict datum from its three components: a cover-map realization, the
finiteness proposition, and the two strict laws. -/
noncomputable def S1788StrictCoverDataOfParts
    (coverMorphism : ∀ {A B : S1788Cover},
      (A ⟶ B) → A.source.Hom B.source)
    (coverMorphism_over : ∀ {A B : S1788Cover} (f : A ⟶ B),
      Iso (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map) A.map)
    (hFin : S1788FiberFiniteRequired)
    (hLaws : S1788StrictFiberLaws coverMorphism coverMorphism_over) :
    StrictCoverData (F := S1788K) (X := S1788Orbicurve)
      S1788BaseScheme S1788BasePoint where
  coverMorphism := coverMorphism
  coverMorphism_over := coverMorphism_over
  fintype cover := Classical.choice (hFin cover)
  map_id := hLaws.map_id
  map_comp := hLaws.map_comp

/-- R2 from the three explicitly separated parts: a cover-map realization,
the S1780 finiteness input, and the two strict laws. -/
theorem S1788R2_of_finite_and_laws
    (coverMorphism : ∀ {A B : S1788Cover},
      (A ⟶ B) → A.source.Hom B.source)
    (coverMorphism_over : ∀ {A B : S1788Cover} (f : A ⟶ B),
      Iso (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map) A.map)
    (hFin : S1788FiberFiniteRequired)
    (hLaws : S1788StrictFiberLaws coverMorphism coverMorphism_over) :
    Nonempty (@S1754S1726FiberIdentificationMissing
      ‹Category.{0, 1} S1788Cover›
      (S1788FiberFunctor
        (S1788StrictCoverDataOfParts coverMorphism coverMorphism_over
          hFin hLaws))) :=
  ⟨S1788FiberIdentification
    (S1788StrictCoverDataOfParts coverMorphism coverMorphism_over hFin hLaws)⟩

end Decomposition

/-! ## 9. Axiom footprint -/

#print axioms S1788BasePoint
#print axioms S1788FiberFunctor
#print axioms S1788FiberFunctor_map_apply
#print axioms S1788FiberIdentification
#print axioms S1788R2
#print axioms S1788FiberIdentification_natural
#print axioms S1788FiberIdentificationData
#print axioms S1788FiberIdentificationData_nonempty_iff
#print axioms S1788R2_of_fiberIdentificationData
#print axioms S1788FiberIdentificationExists_iff
#print axioms S1788R2_exists_of_exactMissing
#print axioms S1788FiberNatIso
#print axioms S1788FiberNatIso_hom_app
#print axioms S1788R2_of_finite_and_laws
#print axioms S1788StrictCoverDataOfParts

end LeanFormal.IUT.XiFPaper.S1788FiberIdentificationActual