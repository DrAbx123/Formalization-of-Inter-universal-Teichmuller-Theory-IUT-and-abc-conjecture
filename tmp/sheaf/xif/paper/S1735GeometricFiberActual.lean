/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# S1735: the actual geometric fiber functor of the S1726 D6 orbicurve

## Question

Construct, for the actual orbicurve

  X = S1726Orbicurve over F' = S1726K,

the actual geometric fiber functor

  OrbicurveFiniteEtaleCover X  ->  FintypeCat

whose objects are the literal geometric fibers at the actual affine point
(0,0) of the S1726 Weierstrass model and whose morphisms are the literal
geometric-fiber maps induced by actual cover maps.

## What is constructed

* the actual base scheme Spec F' and the actual scheme-valued point at (0,0),
  obtained from the S1726 section S1726OverOfAlgHom and the point
  S1726PointAlgHom 0 0;

* the literal geometric fiber type
  S1735Fiber cover = GeometricFiber baseScheme basePoint cover
  and the literal geometric-fiber map S1735FiberMap;

* the conditional actual functor S1735GeometricFiberFunctor with exactly those
  objects and morphisms, from an explicit strict cover datum: a Category.{0}
  structure, an actual cover map for every categorical arrow, a Fintype
  instance on every literal fiber, and the strict identity/composition
  equalities of the literal fiber maps;

* the theorem that the strict equalities are not an extra geometric
  assumption once the target certificate's fiber-identification fields are
  present: a functor fiber together with pointwise equivalences
  fiber.obj cover ~ GeometricFiber cover and the pointwise naturality
  fiberIdentification_natural forces the strict laws.  Thus the strict cover
  datum is derived from the target certificate, not postulated;

* the reduction of Mathlib's PreGaloisCategory.FiberFunctor to its six
  explicit preservation fields (terminal, pullbacks, finite coproducts,
  epimorphisms, finite-group quotients, reflection of isomorphisms), and the
  conditional construction of the Mathlib FiberFunctor and GaloisCategory for
  the actual geometric fiber functor.

## Exact first missing

The construction is not unconditional.  In dependency order the missing
inputs are:

1. a Category.{0,1} structure on the actual cover type.  S1728 proves that
   this is equivalent to small raw cover-map carriers, and no such carriers
   are constructed here; S1735CoverCategoryOfSmallRawData reuses S1728 to
   build the category from that exact input;

2. the Fintype instances on the literal geometric fibers
   (S1735GeometricFiberFintypeRequired).  The tree has the finite-etale
   representability property but not yet the comparison of the 2-fiber with
   the scheme-theoretic finite fiber;

3. the six preservation fields of Mathlib's FiberFunctor for the resulting
   functor, together with a PreGaloisCategory structure on the cover category
   (finite limits, finite coproducts and finite-group quotients).

No fiber, no category and no Galois structure is faked.  The literal geometric
fibers and maps are the definitions from Iut/Foundations/Orbicurve.lean; the
conditional functor is a genuine functor with exactly those objects and maps.

## Axiom footprint

Only propext, Classical.choice and Quot.sound are used; see the #print axioms
block at the end.  No sorry, axiom or admit is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

universe u v w

/-! ## 1. Strong transformations of representable pseudofunctors -/

/-- Natural transformations between functors into a discrete category are
subsingleton. -/
instance subsingletonNatTrans_of_isDiscrete
    {C : Type v} [Category.{w} C] {D : Type u} [Category.{w} D] [IsDiscrete D]
    (F G : C ⥤ D) : Subsingleton (F ⟶ G) := by
  constructor
  intro α β
  apply NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- 2-morphisms in Cat into a discrete category are subsingleton. -/
instance subsingletonCatHom₂_of_isDiscrete
    {C D : Cat.{w, u}} [IsDiscrete ↑D] (F G : C ⟶ D) :
    Subsingleton (F ⟶ G) := by
  constructor
  intro α β
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- Postcomposition with a scheme morphism gives a functor between the
representable discrete fibers. -/
noncomputable def postFiber
    {F : Type u} [Field F]
    {S T : SchemeOverField F} (s : S ⟶ T)
    (U : (SchemeOverField F)ᵒᵖ) :
    (schemeRepresentableFiberFunctor F S).obj U ⟶
      (schemeRepresentableFiberFunctor F T).obj U :=
  (Discrete.functor
    (fun P : Opposite.unop U ⟶ S => Discrete.mk (P ≫ s))).toCatHom

/-- The strong transformation of representable pseudofunctors induced by a
scheme morphism. -/
noncomputable def representableStrongTrans
    {F : Type u} [Field F]
    {S T : SchemeOverField F} (s : S ⟶ T) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F S)
      (schemeRepresentableEtalePseudofunctor F T) where
  app U := postFiber s U.as
  naturality {a b} f := by
    obtain ⟨f⟩ := f
    apply eqToIso
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro P
      obtain ⟨P⟩ := P
      apply Discrete.ext
      simp only [schemeRepresentableEtalePseudofunctor,
        Functor.toPseudofunctor'_map, schemeRepresentableFiberFunctor,
        postFiber, Discrete.functor]
      rfl
    · intro P Q h
      haveI : IsDiscrete ↑((schemeRepresentableEtalePseudofunctor F T).obj b) := by
        change IsDiscrete (Discrete (Opposite.unop b.as ⟶ T))
        infer_instance
      exact Subsingleton.elim _ _
  naturality_naturality {a b f g} η := by
    obtain rfl := obj_ext_of_isDiscrete η
    haveI : IsDiscrete ↑((schemeRepresentableEtalePseudofunctor F T).obj b) := by
      change IsDiscrete (Discrete (Opposite.unop b.as ⟶ T))
      infer_instance
    exact Subsingleton.elim _ _
  naturality_id a := by
    haveI : IsDiscrete ↑((schemeRepresentableEtalePseudofunctor F T).obj a) := by
      change IsDiscrete (Discrete (Opposite.unop a.as ⟶ T))
      infer_instance
    exact Subsingleton.elim _ _
  naturality_comp {a b c} f g := by
    haveI : IsDiscrete ↑((schemeRepresentableEtalePseudofunctor F T).obj c) := by
      change IsDiscrete (Discrete (Opposite.unop c.as ⟶ T))
      infer_instance
    exact Subsingleton.elim _ _

/-! ## 2. The literal geometric fiber type and map -/

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- The actual geometric fiber of a cover at a scheme-valued point. -/
abbrev GeomFiber (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) : Type u :=
  OrbicurveFiniteEtaleCover.GeometricFiber baseScheme point cover

/-- The actual map on geometric fibers induced by an actual cover map. -/
noncomputable def geomFiberMap (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    {source target : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap source target) :
    GeomFiber baseScheme point source → GeomFiber baseScheme point target :=
  fun x =>
    (OrbicurveFiniteEtaleCover.geometricFiberMap
      f.map f.commutes baseScheme point).obj x

/-! ## 3. The strict cover datum and the conditional actual functor -/

section CoverCategory

variable [Category.{u} (OrbicurveFiniteEtaleCover X)]

/-- The strict geometric-fiber data required to define an actual fiber functor
with object map GeomFiber and morphism map geomFiberMap.  The final two fields
are not derivable from the 2-category of cover maps alone: the available data
only gives 2-isomorphisms, not the equalities of functions. -/
structure StrictCoverData
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber) where
  /-- The actual cover map underlying a categorical arrow. -/
  coverMorphism : ∀ {A B : OrbicurveFiniteEtaleCover X},
    (A ⟶ B) → A.source.Hom B.source
  /-- The commuting 2-cell of the underlying cover map. -/
  coverMorphism_over : ∀ {A B : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B),
    Iso
      (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map)
      A.map
  /-- Finiteness of the actual geometric fiber. -/
  fintype : ∀ cover : OrbicurveFiniteEtaleCover X,
    Fintype (GeomFiber baseScheme point cover)
  /-- Strict identity law for the actual geometric fiber map. -/
  map_id : ∀ cover : OrbicurveFiniteEtaleCover X,
    geomFiberMap baseScheme point
        (⟨coverMorphism (𝟙 cover), coverMorphism_over (𝟙 cover)⟩ :
          OrbicurveFiniteEtaleCoverMap cover cover) = id
  /-- Strict composition law for the actual geometric fiber map. -/
  map_comp : ∀ {A B C : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B) (g : B ⟶ C),
    geomFiberMap baseScheme point
        (⟨coverMorphism (f ≫ g), coverMorphism_over (f ≫ g)⟩ :
          OrbicurveFiniteEtaleCoverMap A C) =
      geomFiberMap baseScheme point
          (⟨coverMorphism g, coverMorphism_over g⟩ :
            OrbicurveFiniteEtaleCoverMap B C) ∘
        geomFiberMap baseScheme point
          (⟨coverMorphism f, coverMorphism_over f⟩ :
            OrbicurveFiniteEtaleCoverMap A B)

/-- The finite type of the actual geometric fiber, under the strict data. -/
noncomputable def fiberFintypeCat
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    (cover : OrbicurveFiniteEtaleCover X) : FintypeCat.{u} :=
  letI : Fintype (GeomFiber baseScheme point cover) := D.fintype cover
  FintypeCat.of (GeomFiber baseScheme point cover)

/-- The actual geometric fiber functor, conditional on the strict cover
datum.  Its objects are the actual geometric fibers and its morphisms are the
actual geometric-fiber maps. -/
noncomputable def geometricFiberFunctor
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point) :
    OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u} where
  obj cover := fiberFintypeCat baseScheme point D cover
  map {A B} f :=
    FintypeCat.homMk
      (geomFiberMap baseScheme point
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B))
  map_id A := by
    apply FintypeCat.hom_ext
    intro x
    exact congrFun (D.map_id A) x
  map_comp {A B C} f g := by
    apply FintypeCat.hom_ext
    intro x
    exact congrFun (D.map_comp f g) x

@[simp] theorem geometricFiberFunctor_obj
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    (cover : OrbicurveFiniteEtaleCover X) :
    (geometricFiberFunctor baseScheme point D).obj cover =
      fiberFintypeCat baseScheme point D cover := rfl

@[simp] theorem geometricFiberFunctor_map_apply
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    {A B : OrbicurveFiniteEtaleCover X} (f : A ⟶ B)
    (x : GeomFiber baseScheme point A) :
    (geometricFiberFunctor baseScheme point D).map f x =
      geomFiberMap baseScheme point
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B) x := rfl

/-! ## 4. The target fiber identification forces the strict laws -/

/-- The fiber-side fields of the target certificate, isolated: a stored fiber
functor, pointwise equivalences with the literal geometric fibers, and their
pointwise naturality. -/
structure FiberIdentificationData
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber) where
  coverMorphism : ∀ {A B : OrbicurveFiniteEtaleCover X},
    (A ⟶ B) → A.source.Hom B.source
  coverMorphism_over : ∀ {A B : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B),
    Iso
      (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map)
      A.map
  fiber : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}
  fiberIdentification : ∀ cover : OrbicurveFiniteEtaleCover X,
    (fiber.obj cover).obj ≃ GeomFiber baseScheme point cover
  fiberIdentification_natural : ∀ {A B : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B) (x : (fiber.obj A).obj),
    fiberIdentification B (fiber.map f x) =
      geomFiberMap baseScheme point
        (⟨coverMorphism f, coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B)
        (fiberIdentification A x)

/-- The inverse naturality form of the fiber identification. -/
theorem fiberIdentification_symm_natural
    {baseScheme : SchemeOverField F}
    {point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber}
    (D : FiberIdentificationData (F := F) (X := X) baseScheme point)
    {A B : OrbicurveFiniteEtaleCover X} (f : A ⟶ B)
    (y : (D.fiber.obj A).obj) :
    (D.fiberIdentification B).symm
      (geomFiberMap baseScheme point
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B)
        (D.fiberIdentification A y)) =
    D.fiber.map f y := by
  apply (D.fiberIdentification B).injective
  rw [Equiv.apply_symm_apply, D.fiberIdentification_natural]

/-- The fiber identification implies the strict geometric-fiber data.  The
strict identity and composition laws are forced by the functor laws of the
stored fiber functor and the pointwise naturality of the identification. -/
noncomputable def strictCoverDataOfFiberIdentification
    {baseScheme : SchemeOverField F}
    {point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber}
    (D : FiberIdentificationData (F := F) (X := X) baseScheme point) :
    StrictCoverData (F := F) (X := X) baseScheme point where
  coverMorphism := D.coverMorphism
  coverMorphism_over := D.coverMorphism_over
  fintype cover := by
    letI : Fintype (D.fiber.obj cover).obj := FintypeCat.fintype
    exact Fintype.ofEquiv (D.fiber.obj cover).obj (D.fiberIdentification cover)
  map_id cover := by
    funext x
    apply (D.fiberIdentification cover).symm.injective
    have hx : D.fiberIdentification cover ((D.fiberIdentification cover).symm x) = x :=
      Equiv.apply_symm_apply _ x
    rw [← hx]
    rw [fiberIdentification_symm_natural D (𝟙 cover)]
    have h : D.fiber.map (𝟙 cover) ((D.fiberIdentification cover).symm x) =
        (D.fiberIdentification cover).symm x := by
      simpa using
        congrArg (fun m => m ((D.fiberIdentification cover).symm x))
          (D.fiber.map_id cover)
    simpa only [id_eq, hx] using h
  map_comp {A B C} f g := by
    funext x
    apply (D.fiberIdentification C).symm.injective
    change (D.fiberIdentification C).symm
        (geomFiberMap baseScheme point
          (⟨D.coverMorphism (f ≫ g), D.coverMorphism_over (f ≫ g)⟩ :
            OrbicurveFiniteEtaleCoverMap A C) x) =
      (D.fiberIdentification C).symm
        (geomFiberMap baseScheme point
          (⟨D.coverMorphism g, D.coverMorphism_over g⟩ :
            OrbicurveFiniteEtaleCoverMap B C)
          (geomFiberMap baseScheme point
            (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
              OrbicurveFiniteEtaleCoverMap A B) x))
    have h1 : (D.fiberIdentification C).symm
        (geomFiberMap baseScheme point
          (⟨D.coverMorphism (f ≫ g), D.coverMorphism_over (f ≫ g)⟩ :
            OrbicurveFiniteEtaleCoverMap A C) x) =
        D.fiber.map (f ≫ g) ((D.fiberIdentification A).symm x) := by
      simpa only [Equiv.apply_symm_apply] using
        fiberIdentification_symm_natural D (f ≫ g)
          ((D.fiberIdentification A).symm x)
    have h2 : (D.fiberIdentification C).symm
        (geomFiberMap baseScheme point
          (⟨D.coverMorphism g, D.coverMorphism_over g⟩ :
            OrbicurveFiniteEtaleCoverMap B C)
          (geomFiberMap baseScheme point
            (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
              OrbicurveFiniteEtaleCoverMap A B) x)) =
        D.fiber.map g (D.fiber.map f ((D.fiberIdentification A).symm x)) := by
      calc
        (D.fiberIdentification C).symm
            (geomFiberMap baseScheme point
              (⟨D.coverMorphism g, D.coverMorphism_over g⟩ :
                OrbicurveFiniteEtaleCoverMap B C)
              (geomFiberMap baseScheme point
                (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
                  OrbicurveFiniteEtaleCoverMap A B) x))
            = D.fiber.map g
                ((D.fiberIdentification B).symm
                  (geomFiberMap baseScheme point
                    (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
                      OrbicurveFiniteEtaleCoverMap A B) x)) := by
                simpa only [Equiv.apply_symm_apply] using
                  fiberIdentification_symm_natural D g
                    ((D.fiberIdentification B).symm
                      (geomFiberMap baseScheme point
                        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
                          OrbicurveFiniteEtaleCoverMap A B) x))
        _ = D.fiber.map g (D.fiber.map f ((D.fiberIdentification A).symm x)) := by
                congr 1
                simpa only [Equiv.apply_symm_apply] using
                  fiberIdentification_symm_natural D f
                    ((D.fiberIdentification A).symm x)
    rw [h1, h2]
    simpa only [FintypeCat.comp_apply] using
      congrArg (fun m => m ((D.fiberIdentification A).symm x))
        (D.fiber.map_comp f g)

/-! ## 5. Mathlib FiberFunctor reduced to six preservation fields -/

variable [PreGaloisCategory (OrbicurveFiniteEtaleCover X)]

/-- The exact preservation fields of Mathlib's fiber-functor class. -/
structure FiberFunctorAxioms
    (G : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}) where
  preservesTerminalObjects :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) G
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan G
  preservesFiniteCoproducts : PreservesFiniteCoproducts G
  preservesEpis : Functor.PreservesEpimorphisms G
  preservesQuotientsByFiniteGroups : ∀ (H : Type u) [Group H] [Finite H],
    PreservesColimitsOfShape (SingleObj H) G
  reflectsIsos : G.ReflectsIsomorphisms

/-- The Mathlib fiber-functor class from its six explicit preservation fields. -/
theorem fiberFunctorOfAxioms
    {G : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}}
    (A : FiberFunctorAxioms G) :
    PreGaloisCategory.FiberFunctor G where
  preservesTerminalObjects := A.preservesTerminalObjects
  preservesPullbacks := A.preservesPullbacks
  preservesFiniteCoproducts := A.preservesFiniteCoproducts
  preservesEpis := A.preservesEpis
  preservesQuotientsByFiniteGroups := A.preservesQuotientsByFiniteGroups
  reflectsIsos := A.reflectsIsos

/-- The Mathlib fiber-functor class is exactly the six preservation fields. -/
theorem nonemptyFiberFunctor_iff
    (G : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}) :
    Nonempty (PreGaloisCategory.FiberFunctor G) ↔
      Nonempty (FiberFunctorAxioms G) := by
  constructor
  · rintro ⟨inst⟩
    exact ⟨{ preservesTerminalObjects := inst.preservesTerminalObjects
             preservesPullbacks := inst.preservesPullbacks
             preservesFiniteCoproducts := inst.preservesFiniteCoproducts
             preservesEpis := inst.preservesEpis
             preservesQuotientsByFiniteGroups :=
               inst.preservesQuotientsByFiniteGroups
             reflectsIsos := inst.reflectsIsos }⟩
  · rintro ⟨A⟩
    exact ⟨fiberFunctorOfAxioms A⟩

/-- A Galois category from a PreGaloisCategory structure and the six explicit
fiber-functor axioms. -/
theorem galoisCategoryOfAxioms
    (G : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u})
    (A : FiberFunctorAxioms G) :
    GaloisCategory (OrbicurveFiniteEtaleCover X) where
  toPreGaloisCategory := inferInstance
  hasFiberFunctor := ⟨G, ⟨fiberFunctorOfAxioms A⟩⟩

end CoverCategory

/-! ## 6. The actual S1726 orbicurve and the actual point (0,0) -/

namespace Paper

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-- The actual base field F' of S1726. -/
abbrev S1735K : Type := S1726K

/-- The actual orbicurve X = S1726Orbicurve. -/
abbrev S1735Orbicurve : HyperbolicOrbicurve S1735K := S1726Orbicurve

/-- The actual base scheme Spec F'. -/
abbrev S1735BaseScheme : SchemeOverField S1735K := S1726Base

/-- The actual section at the affine point (0,0) of E'. -/
noncomputable def S1735PointSection : S1726Base ⟶ S1726AffineOver :=
  S1726OverOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero)

/-- The actual base point of the S1726 orbicurve at (0,0): the scheme-valued
point of X induced by the actual section at the affine point. -/
noncomputable def S1735BasePoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme)
      S1735Orbicurve.stack.fiber := by
  change Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme)
    (schemeRepresentableEtalePseudofunctor S1735K S1726AffineOver)
  exact representableStrongTrans S1735PointSection

/-- The actual finite-etale-cover type of X. -/
abbrev S1735Cover : Type 1 := OrbicurveFiniteEtaleCover S1735Orbicurve

/-- The actual geometric fiber type at the actual point (0,0). -/
abbrev S1735Fiber (cover : S1735Cover) : Type :=
  GeomFiber (F := S1735K) (X := S1735Orbicurve) S1735BaseScheme S1735BasePoint cover

/-- The actual map on geometric fibers induced by an actual cover map. -/
noncomputable def S1735FiberMap
    {source target : S1735Cover}
    (f : OrbicurveFiniteEtaleCoverMap source target) :
    S1735Fiber source → S1735Fiber target :=
  geomFiberMap (F := S1735K) (X := S1735Orbicurve)
    S1735BaseScheme S1735BasePoint f

/-- The exact finiteness input for the actual geometric fiber. -/
def S1735GeometricFiberFintypeRequired : Prop :=
  ∀ cover : S1735Cover, Nonempty (Fintype (S1735Fiber cover))

/-- The conditional actual geometric fiber functor at the actual base point:
objects are the actual geometric fibers and morphisms are the actual
geometric-fiber maps.  The strict cover datum is the precise missing input. -/
noncomputable def S1735GeometricFiberFunctor
    [Category.{0, 1} S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint) :
    S1735Cover ⥤ FintypeCat.{0} :=
  geometricFiberFunctor (F := S1735K) (X := S1735Orbicurve)
    S1735BaseScheme S1735BasePoint D

@[simp] theorem S1735GeometricFiberFunctor_obj
    [Category.{0, 1} S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)
    (cover : S1735Cover) :
    (S1735GeometricFiberFunctor D).obj cover =
      fiberFintypeCat (F := S1735K) (X := S1735Orbicurve)
        S1735BaseScheme S1735BasePoint D cover := rfl

/-- The underlying type of the functor's object is exactly the literal
geometric fiber at the actual point (0,0). -/
@[simp] theorem S1735GeometricFiberFunctor_obj_obj
    [Category.{0, 1} S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)
    (cover : S1735Cover) :
    ((S1735GeometricFiberFunctor D).obj cover).obj = S1735Fiber cover := rfl

@[simp] theorem S1735GeometricFiberFunctor_map_apply
    [Category.{0, 1} S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)
    {source target : S1735Cover} (f : source ⟶ target)
    (x : S1735Fiber source) :
    (S1735GeometricFiberFunctor D).map f x =
      S1735FiberMap
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap source target) x := rfl

/-! ## 7. Extraction from an actual orbicurve fundamental-group certificate -/

variable {G : ProfiniteGrp.{0}}
variable (D : Iut.OrbicurveEtaleFundamentalGroup S1735Orbicurve G)

/-- The fiber-side fields of an actual orbicurve fundamental-group certificate:
the stored fiber functor, the pointwise identification with the literal
geometric fibers, and its naturality. -/
noncomputable def fiberIdentificationDataOfEtaleFundamentalGroup :
    letI := D.coverCategory
    FiberIdentificationData (F := S1735K) (X := S1735Orbicurve)
      D.baseScheme D.basePoint := by
  letI := D.coverCategory
  exact
    { coverMorphism := D.coverMorphism
      coverMorphism_over := D.coverMorphism_over
      fiber := D.fiber
      fiberIdentification := D.fiberIdentification
      fiberIdentification_natural := D.fiberIdentification_natural }

/-- The strict geometric-fiber datum extracted from the certificate.  This is
where the certificate's pointwise naturality cancels the 2-categorical
strictness obstruction. -/
noncomputable def strictCoverDataOfEtaleFundamentalGroup :
    letI := D.coverCategory
    StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      D.baseScheme D.basePoint := by
  letI := D.coverCategory
  exact strictCoverDataOfFiberIdentification
    (fiberIdentificationDataOfEtaleFundamentalGroup D)

/-- The actual geometric fiber functor extracted from a certificate.  Its
objects are the literal geometric fibers and its morphisms are the literal
geometric-fiber maps; the certificate's stored fiber functor supplies the
strict coherence, re-expressed on the literal fibers. -/
noncomputable def geometricFiberFunctorOfEtaleFundamentalGroup :
    letI := D.coverCategory
    S1735Cover ⥤ FintypeCat.{0} := by
  letI := D.coverCategory
  exact geometricFiberFunctor (F := S1735K) (X := S1735Orbicurve)
    D.baseScheme D.basePoint
    (strictCoverDataOfEtaleFundamentalGroup D)

/-! ## 8. The exact first missing data -/

/-- The literal first missing cover-category datum: small raw cover-map
carriers (S1728). -/
abbrev S1735SmallRawCoverDataRequired : Prop :=
  LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728SmallRawCoverDataRequired

/-- A chosen small raw cover-map family from the required datum. -/
noncomputable def S1735SmallRawFamily
    (h : S1735SmallRawCoverDataRequired) (A B : S1735Cover) : Type :=
  (Classical.choice (h A B)).Carrier

/-- The equivalence from the chosen small carrier to the actual cover maps. -/
noncomputable def S1735SmallRawEquiv
    (h : S1735SmallRawCoverDataRequired) (A B : S1735Cover) :
    S1735SmallRawFamily h A B ≃ OrbicurveFiniteEtaleCoverMap A B :=
  (Classical.choice (h A B)).equiv

/-- The conditional actual small cover category: from small raw cover-map
carriers, the 2-isomorphism quotient is a genuine Category.{0,1} on the actual
cover type (S1728). -/
@[reducible] noncomputable def S1735CoverCategoryOfSmallRawData
    (h : S1735SmallRawCoverDataRequired) : Category.{0, 1} S1735Cover :=
  LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728ActualCategory01
    (S1735SmallRawFamily h) (S1735SmallRawEquiv h)

/-- The exact first missing input for the actual geometric fiber functor:
a Category.{0,1} cover structure together with the strict geometric-fiber datum
at the actual point (0,0). -/
def S1735StrictDataRequired : Prop :=
  ∃ (C : Category.{0, 1} S1735Cover),
    letI := C
    Nonempty (StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)

/-- The exact remaining input on the PreGaloisCategory side: the cover
category must have finite limits, finite coproducts and finite-group
quotients. -/
def S1735PreGaloisCategoryRequired
    (C : Category.{0, 1} S1735Cover) : Prop :=
  @PreGaloisCategory S1735Cover C

/-- The exact remaining input on the fiber functor side: the six explicit
preservation fields of Mathlib's FiberFunctor class. -/
def S1735FiberFunctorAxiomsRequired
    [Category.{0, 1} S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint) : Prop :=
  Nonempty (FiberFunctorAxioms (S1735GeometricFiberFunctor D))

/-- Conditional PreGalois-category fiber functor: the literal geometric fiber
functor is a Mathlib FiberFunctor once the six preservation fields are given. -/
theorem S1735FiberFunctorOfStrictData
    [Category.{0, 1} S1735Cover]
    [PreGaloisCategory S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)
    (A : FiberFunctorAxioms (S1735GeometricFiberFunctor D)) :
    Nonempty (PreGaloisCategory.FiberFunctor (S1735GeometricFiberFunctor D)) :=
  ⟨fiberFunctorOfAxioms A⟩

/-- Conditional Galois category: the actual S1726 cover type is a Mathlib
GaloisCategory once the cover category, its PreGalois structure and the six
fiber-functor axioms are supplied. -/
theorem S1735GaloisCategoryOfStrictData
    [Category.{0, 1} S1735Cover]
    [PreGaloisCategory S1735Cover]
    (D : StrictCoverData (F := S1735K) (X := S1735Orbicurve)
      S1735BaseScheme S1735BasePoint)
    (A : FiberFunctorAxioms (S1735GeometricFiberFunctor D)) :
    GaloisCategory S1735Cover :=
  galoisCategoryOfAxioms _ A

end Paper

/-! ## 9. Axiom footprint -/

#print axioms Paper.S1735BasePoint
#print axioms Paper.S1735FiberMap
#print axioms Paper.S1735GeometricFiberFunctor
#print axioms strictCoverDataOfFiberIdentification
#print axioms nonemptyFiberFunctor_iff
#print axioms Paper.S1735FiberFunctorOfStrictData
#print axioms Paper.S1735GaloisCategoryOfStrictData
#print axioms Paper.geometricFiberFunctorOfEtaleFundamentalGroup

end LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
