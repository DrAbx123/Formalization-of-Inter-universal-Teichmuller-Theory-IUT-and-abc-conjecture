/-
# S1795: strictification of the S1764 geometric fiber functor

## Question

S1764 left four missing inputs for `S1736ActualFiberFunctorObligation`:

1. `S1764FiberFiniteObligation` (actual geometric finiteness; parallel S1735);
2. `S1764FiberMapWellDefinedObligation` (descent through the S1728
   2-isomorphism quotient of the cover maps);
3. `S1764RawIdentityObligation`;
4. `S1764RawCompositionObligation`.

This file settles 3 and 4 outright and reduces 2 exactly.

## Results

* `S1795RawIdentityObligation : S1764RawIdentityObligation`.  The raw
  geometric-fiber map of the canonical identity cover map `S1641CoverMapId` is
  *equal* to the identity function on the geometric fiber -- a strict equality
  of functions, not the natural isomorphism already proved in S1764.  The
  comparison 2-cell of `S1641CoverMapId` is the bicategorical left unitor,
  whose components are the functor left unitors; with the right unitor inserted
  by `geometricFiberMap` it becomes the identity, and the costructured-arrow
  object is left unchanged.

* `S1795RawCompositionObligation : S1764RawCompositionObligation`.  For the
  canonical composite `S1641CoverMapComp f g` the raw geometric-fiber map is
  *equal* to the composite of the two raw maps.  The composite comparison
  2-cell of S1641 is the associator, then the left whiskering of `g.commutes`,
  then `f.commutes`; the functor associator and the two functor unitors are
  componentwise identities, and Cat's `whiskerLeft_app` identifies the
  whiskered component with `g.commutes.app (f.map.app site .obj x.left)`, which is
  exactly the object argument of the second raw map.

* `S1795FiberMapWellDefined_iff`:
  `S1764FiberMapWellDefinedObligation` is equivalent to the conjunction of

  - `S1795StrictObjectMapAgreement`: on 2-isomorphic cover maps the *object
    maps* of the underlying component functors agree strictly, and
  - `S1795StrictHomAgreement`: the induced comparison morphisms agree.

  In particular (`S1795WellDefined_forces_strict_objmap`) well-definedness
  forces the strict equality
  `(f.map.app site).toFunctor.obj x.left = (g.map.app site).toFunctor.obj x.left`.

## Why the well-definedness obligation is a genuine gap, not a coherence

`S1728CoverMapRel f g` is `Nonempty (f.map ≅ g.map)`: a 2-isomorphism of
the underlying strong transformations.  At each site such a 2-isomorphism gives
an isomorphism of functors `f.map.app site ≅ g.map.app site`, hence only an
isomorphism between the images of a fiber object -- not an equality.  But the
raw geometric-fiber map uses the *object* `(f.map.app site).toFunctor.obj x.left`
as the left component of a costructured arrow
(`S1795RawFiberFunctor_obj_left`), and it uses the commuting 2-cell `commutes`
as the comparison morphism of that arrow.  Neither datum is determined by the
S1728 class: the relation forgets `commutes` entirely and remembers `f.map`
only up to 2-isomorphism.

Hence `S1764FiberMapWellDefinedObligation` cannot be obtained by cancelling
2-isomorphisms inside the quotient.  It is exactly the strictification of the
pseudofunctor: for every 2-isomorphism of cover maps one must supply an
equality of the two raw images.  This file records that input precisely as
`S1795StrictObjectMapAgreement ∧ S1795StrictHomAgreement`, proves the
equivalence, and does not assert it.

## Consequence

`S1795ConcreteFiberFunctorMissing_iff`:
`S1764ConcreteFiberFunctorMissing` is equivalent to
`S1764FiberFiniteObligation ∧ S1764FiberMapWellDefinedObligation`; the two
strict laws are proved here, so only geometric finiteness (S1735) and the
strictification input remain.

## Honest boundary

No sorry, no axiom, no fake fiber, no fabricated strict law.  The two strict
laws are real equalities of functions; the well-definedness obligation is not
asserted, its exact content is identified.
-/

import tmp.sheaf.xif.paper.S1764ActualFiberFunctorActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/- The geometric fiber is a `CostructuredArrow` in the bicategory `Cat`, where
1-morphisms are wrapped as `Cat.Hom` and 2-morphisms as `Cat.Hom₂`.  The
compatibility flag below keeps the `Cat` coercions and the `CostructuredArrow`
comma projections definitionally transparent in the object computations; it
does not change any statement. -/
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1795StrictFiberFunctorActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

/-! ## 1. The general strict laws for `geometricFiberMap`

The two laws hold for an arbitrary field `F`, orbicurve `X`, base scheme and
base point; the S1764 obligations are their specialisations. -/

section General

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- **Strict identity law.**  The raw geometric-fiber map of the canonical
identity cover map is the identity function on the geometric fiber.  This is a
strict equality, improving the natural isomorphism of S1764. -/
theorem geometricFiberMap_id_strict
    (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapId cover).map (S1641CoverMapId cover).commutes
        scheme point).obj x) = id := by
  funext x
  dsimp only [S1641CoverMapId, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  simp only [Functor.id_obj, Pseudofunctor.StrongTrans.comp_app, eqToHom_refl,
    Pseudofunctor.StrongTrans.isoMk_hom_as_app, Category.id_comp,
    Cat.leftUnitor_hom_toNatTrans, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.id_map, Discrete.natTrans_app, id_eq]
  erw [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

/-- **Strict composition law.**  For the canonical composite of two actual cover
maps, the raw geometric-fiber map is the composite of the two raw maps.  Again
a strict equality of functions. -/
theorem geometricFiberMap_comp_strict
    (scheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F scheme) X.stack.fiber)
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
        (S1641CoverMapComp f g).map (S1641CoverMapComp f g).commutes
        scheme point).obj x)
      = (fun x => (OrbicurveFiniteEtaleCover.geometricFiberMap
          g.map g.commutes scheme point).obj
            ((OrbicurveFiniteEtaleCover.geometricFiberMap
              f.map f.commutes scheme point).obj x)) := by
  funext x
  dsimp only [S1641CoverMapComp, OrbicurveFiniteEtaleCover.geometricFiberMap,
    CostructuredArrow.map₂, Comma.map]
  refine Comma.ext rfl rfl ?_
  apply heq_of_eq
  dsimp only
  rw [S1641CoverMapComp_commutes_hom_app]
  simp
  erw [Category.id_comp]
  try erw [Category.comp_id]
  try erw [Category.comp_id]
  try erw [Category.comp_id]

end General

/-! ## 2. The two named S1764 obligations -/

/-- S1764's strict identity obligation holds. -/
theorem S1795RawIdentityObligation : S1764RawIdentityObligation := by
  intro cover
  exact geometricFiberMap_id_strict (F := S1764K) (X := S1764Orbicurve)
    S1764BaseScheme S1764BasePoint cover

/-- S1764's strict composition obligation holds. -/
theorem S1795RawCompositionObligation : S1764RawCompositionObligation := by
  intro A B C f g
  exact geometricFiberMap_comp_strict (F := S1764K) (X := S1764Orbicurve)
    S1764BaseScheme S1764BasePoint f g

/-! ## 3. The well-definedness obligation: exact content

`S1764RawFiberMap f` is the object function of `geometricFiberMap f.map
f.commutes`.  Its value at a costructured arrow `x` has left component
`(f.map.app site).toFunctor.obj x.left` and comparison component built from
`f.commutes`.  The next propositions isolate the two halves of the
well-definedness obligation. -/

/-- The left (object) component of a raw geometric fiber is literally the object
map of the underlying component functor. -/
theorem S1795RawFiberFunctor_obj_left
    {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B) (x : S1764Fiber A) :
    ((S1764RawFiberFunctor f).obj x).left =
      (f.map.app (LocallyDiscrete.mk (Opposite.op S1764BaseScheme))).toFunctor.obj
        x.left := rfl

/-- Equal costructured arrows have heq-equal comparison components. -/
theorem S1795HeqHomOfEq
    {B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    {X Y : S1764Fiber B} (h : X = Y) : HEq X.hom Y.hom := by
  cases h
  exact HEq.rfl

/-- Strict agreement of the object maps of the underlying component functors on
2-isomorphic cover maps.  This is the half of well-definedness that a
2-isomorphism does not supply. -/
def S1795StrictObjectMapAgreement : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f g : OrbicurveFiniteEtaleCoverMap A B),
    S1728CoverMapRel f g → ∀ x : S1764Fiber A,
      ((S1764RawFiberFunctor f).obj x).left =
        ((S1764RawFiberFunctor g).obj x).left

/-- Agreement of the comparison (commuting 2-cell) components of the raw
geometric fibers of 2-isomorphic cover maps.  This is the half of
well-definedness that involves `commutes`, which `S1728CoverMapRel` forgets. -/
def S1795StrictHomAgreement : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f g : OrbicurveFiniteEtaleCoverMap A B),
    S1728CoverMapRel f g → ∀ x : S1764Fiber A,
      HEq ((S1764RawFiberFunctor f).obj x).hom
        ((S1764RawFiberFunctor g).obj x).hom

/-- The well-definedness obligation forces strict equality of the object maps of
the underlying 1-morphisms, not merely the 2-isomorphism supplied by
`S1728CoverMapRel`. -/
theorem S1795WellDefined_forces_strict_objmap
    (h : S1764FiberMapWellDefinedObligation)
    {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    {f g : OrbicurveFiniteEtaleCoverMap A B}
    (hrel : S1728CoverMapRel f g) (x : S1764Fiber A) :
    (f.map.app (LocallyDiscrete.mk (Opposite.op S1764BaseScheme))).toFunctor.obj
        x.left =
      (g.map.app (LocallyDiscrete.mk (Opposite.op S1764BaseScheme))).toFunctor.obj
        x.left := by
  have hx : (S1764RawFiberFunctor f).obj x = (S1764RawFiberFunctor g).obj x := by
    have h' := congrFun (h f g hrel) x
    simpa only [S1764RawFiberMap] using h'
  have hleft := congrArg (fun z : S1764Fiber B => z.left) hx
  rw [S1795RawFiberFunctor_obj_left, S1795RawFiberFunctor_obj_left] at hleft
  exact hleft

/-- **Exact characterisation of the well-definedness obligation.**  It is
equivalent to the conjunction of strict object-map agreement and comparison
agreement.  Both halves concern data that the S1728 quotient relation does not
record. -/
theorem S1795FiberMapWellDefined_iff :
    S1764FiberMapWellDefinedObligation ↔
      S1795StrictObjectMapAgreement ∧ S1795StrictHomAgreement := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro A B f g hrel x
      have hx : (S1764RawFiberFunctor f).obj x = (S1764RawFiberFunctor g).obj x := by
        have h' := congrFun (h f g hrel) x
        simpa only [S1764RawFiberMap] using h'
      have hleft := congrArg (fun z : S1764Fiber B => z.left) hx
      rw [S1795RawFiberFunctor_obj_left, S1795RawFiberFunctor_obj_left] at hleft
      exact hleft
    · intro A B f g hrel x
      have hx : (S1764RawFiberFunctor f).obj x = (S1764RawFiberFunctor g).obj x := by
        have h' := congrFun (h f g hrel) x
        simpa only [S1764RawFiberMap] using h'
      exact S1795HeqHomOfEq hx
  · rintro ⟨hL, hH⟩ A B f g hrel
    funext x
    exact Comma.ext (hL f g hrel x) rfl (hH f g hrel x)

/-! ## 4. Consequence for the S1764 missing bundle -/

/-- With the two strict laws proved, S1764's four missing inputs reduce to
geometric finiteness and strictification. -/
theorem S1795ConcreteFiberFunctorMissing_iff :
    S1764ConcreteFiberFunctorMissing ↔
      S1764FiberFiniteObligation ∧ S1764FiberMapWellDefinedObligation := by
  constructor
  · rintro ⟨hF, hW, _, _⟩
    exact ⟨hF, hW⟩
  · rintro ⟨hF, hW⟩
    exact ⟨hF, hW, S1795RawIdentityObligation, S1795RawCompositionObligation⟩

/-- The conditional strict fiber data of S1764 now needs only finiteness and
well-definedness. -/
theorem S1795StrictFiberDataNonempty_iff :
    Nonempty S1764StrictFiberData ↔
      S1764FiberFiniteObligation ∧ S1764FiberMapWellDefinedObligation := by
  rw [S1764StrictFiberDataNonempty_iff, S1795ConcreteFiberFunctorMissing_iff]

/-- The actual fibre functor to `FintypeCat.0`, conditional exactly on the two
remaining inputs.  Its object map is the actual geometric fiber. -/
noncomputable def S1795FiberFunctorOfRemaining
    (hF : S1764FiberFiniteObligation)
    (hW : S1764FiberMapWellDefinedObligation) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{0} :=
  S1764FiberFunctorOfObligations hF hW S1795RawIdentityObligation
    S1795RawCompositionObligation

/-- The conditional functor's object map is the actual geometric fiber. -/
@[simp] theorem S1795FiberFunctorOfRemaining_obj
    (hF : S1764FiberFiniteObligation)
    (hW : S1764FiberMapWellDefinedObligation)
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    ((S1795FiberFunctorOfRemaining hF hW).obj cover).obj = S1764Fiber cover := rfl

/-! ## 5. Status and audit -/

#check S1795RawIdentityObligation
#check S1795RawCompositionObligation
#check S1795RawFiberFunctor_obj_left
#check S1795HeqHomOfEq
#check S1795StrictObjectMapAgreement
#check S1795StrictHomAgreement
#check S1795WellDefined_forces_strict_objmap
#check S1795FiberMapWellDefined_iff
#check S1795ConcreteFiberFunctorMissing_iff
#check S1795StrictFiberDataNonempty_iff
#check S1795FiberFunctorOfRemaining
#check S1795FiberFunctorOfRemaining_obj

#print axioms geometricFiberMap_id_strict
#print axioms geometricFiberMap_comp_strict
#print axioms S1795RawIdentityObligation
#print axioms S1795RawCompositionObligation
#print axioms S1795WellDefined_forces_strict_objmap
#print axioms S1795FiberMapWellDefined_iff
#print axioms S1795ConcreteFiberFunctorMissing_iff
#print axioms S1795StrictFiberDataNonempty_iff

end LeanFormal.IUT.XiFPaper.S1795StrictFiberFunctorActual
