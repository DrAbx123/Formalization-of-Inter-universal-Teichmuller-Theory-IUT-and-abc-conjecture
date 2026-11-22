/-
# S1764: the actual geometric fiber functor on the S1726 D6 orbicurve

## Target

S1736 records the fiber-functor obligation

  S1736ActualFiberFunctorObligation P
    = exists Fib : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u+1},
        Nonempty (PreGaloisCategory.FiberFunctor P Fib)

for the actual S1728 2-isomorphism-quotient category.  This file attacks the
concrete geometric candidate for the S1726 orbicurve

  X = S1726Orbicurve over S1726K,
  baseScheme = S1726AffineOver,
  basePoint  = the identity strong transformation (the requested
               S1726AffineOver/id point),

with

  cover ↦ GeometricFiber S1764BaseScheme S1764BasePoint cover
  f     ↦ geometricFiberMap f.map f.commutes S1764BaseScheme S1764BasePoint.

## What is constructed unconditionally

* the actual base point S1764BasePoint : X.stack.fiber at S1726AffineOver
  (the identity strong transformation; S1726Orbicurve.stack.fiber is
  definitionally the representable pseudofunctor of S1726AffineOver);
* the actual geometric fiber type S1764Fiber cover, living in Type (not Type 1);
* the raw geometric-fiber functor S1764RawFiberFunctor f for an actual cover
  map, and its object function S1764RawFiberMap f;
* the natural isomorphism

    S1764RawFiberFunctor (S1641CoverMapId cover) ≅ 𝟭 (S1764Fiber cover);

* the strict-fiber-data structure S1764StrictFiberData, and the conditional
  functors S1764FiberFunctorOfObligations (to FintypeCat.{0}) and
  S1764FiberFunctorULiftOfObligations (to FintypeCat.{1}, the S1736 target
  universe);
* the exact equivalence

    Nonempty S1764StrictFiberData
      ↔ finite fibers ∧ factorization through the 2-isomorphism quotient
        ∧ strict identity law ∧ strict composition law;

* the sufficient implication

    strict fiber data + the six FiberFunctor fields
      ⇒ S1736ActualFiberFunctorObligation P.

## Exact missing (no fake fiber)

The following are NOT inhabited in this file:

1. S1764FiberFiniteObligation:
     forall cover, Finite (S1764Fiber cover).
   This is the actual geometric-fiber finiteness theorem (the parallel S1735
   task; it is not derivable from the present definitions).
2. S1764FiberMapWellDefinedObligation:
     geometricFiberMap is constant on S1728CoverMapRel-classes.
   The S1728 category is a quotient of the actual cover maps by 2-isomorphism.
   The actual geometric-fiber assignment is only pseudofunctorial, so this
   strict factorization is a genuine additional input; it is exactly the
   obstruction for a strict functor out of the 2-isomorphism quotient.
3. S1764RawIdentityObligation and S1764RawCompositionObligation:
     the strict identity/composition equalities for the canonical S1641
     identity and composite actual cover maps.  The identity comparison is
     proved below only as a natural isomorphism, and the composite comparison
     is not constructed; the raw functors are only pseudofunctorial.
4. the six PreGaloisCategory.FiberFunctor fields for the resulting functor
   (preservation of terminal objects, pullbacks, finite coproducts,
   epimorphisms, finite-group quotients, and reflection of isomorphisms).
   These are separate geometric properties; the file records the exact
   residual as S1764FiberFunctorAxiomsObligation.

## Universe finding

GeometricFiber is the object type of a CostructuredArrow category in
Cat.{u,u}; for F = S1726K : Type it is Type 0.  The literal
S1736ActualFiberFunctorObligation at the S1728 Category.{1,1} asks for
FintypeCat.{1}.  Therefore the literal S1736 target needs the universe lift
ULift.{1,0} of the actual fiber (an equivalence of finite types, not a
different or fake fiber).  Both the unlifted functor to FintypeCat.{0} and the
lifted functor to FintypeCat.{1} are constructed conditionally.

## Honest boundary

No sorry, no axiom, no fake fiber, no PUnit/unit fiber, no assertion that a
geometric fiber is finite.  The S1736 obligation is not claimed to be
inhabited; its concrete geometric reduction is recorded exactly.
-/

import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual
import Mathlib.CategoryTheory.FintypeCat

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

/-! ## 0. The actual base data -/

/-- The actual base field F' of S1726. -/
abbrev S1764K : Type := S1726K

/-- The actual D6 orbicurve of S1726. -/
abbrev S1764Orbicurve : HyperbolicOrbicurve S1764K := S1726Orbicurve

/-- The requested base scheme: the affine model S1726AffineOver itself. -/
abbrev S1764BaseScheme : SchemeOverField S1764K := S1726AffineOver

/-- The requested base point S1726AffineOver/id: the identity strong
transformation.  The stack fiber of S1726Orbicurve is definitionally the
representable pseudofunctor of S1726AffineOver, so the identity is a genuine
scheme-valued point of the orbicurve. -/
noncomputable def S1764BasePoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1764K S1764BaseScheme)
      S1764Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- The actual geometric fiber of a cover at S1726AffineOver/id.  This is the
literal CostructuredArrow fiber, in Type 0. -/
abbrev S1764Fiber (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) : Type :=
  OrbicurveFiniteEtaleCover.GeometricFiber
    S1764BaseScheme S1764BasePoint cover

/-- The S1728 actual category on the cover type: objects Type 1, homs Type 1
(2-isomorphism classes of actual cover maps).  This is the source category of
the S1736 fiber-functor obligation. -/
abbrev S1764ActualCategory :
    Category.{1, 1} (OrbicurveFiniteEtaleCover S1764Orbicurve) :=
  S1728CoverCategory11 (F := S1764K) (X := S1764Orbicurve)

/-- The same category, recorded through the S1736 abbreviation. -/
theorem S1764ActualCategory_eq :
    S1764ActualCategory =
      S1736ActualCategory (F := S1764K) (X := S1764Orbicurve) := rfl

/-! ## 1. The raw geometric-fiber assignment -/

/-- The actual functor on geometric fibers induced by an actual cover map. -/
noncomputable def S1764RawFiberFunctor
    {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    S1764Fiber A ⥤ S1764Fiber B :=
  OrbicurveFiniteEtaleCover.geometricFiberMap
    f.map f.commutes S1764BaseScheme S1764BasePoint

/-- The underlying function of S1764RawFiberFunctor: exactly
geometricFiberMap on objects. -/
noncomputable def S1764RawFiberMap
    {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    S1764Fiber A → S1764Fiber B :=
  fun x => (S1764RawFiberFunctor f).obj x

/-- Natural isomorphism for the canonical actual identity cover map.  This is
the pseudofunctor identity coherence, transported to the geometric fiber:
the raw identity map is naturally isomorphic to the identity functor. -/
theorem S1764RawFiberFunctor_id_natIso
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    Nonempty (S1764RawFiberFunctor
      (S1641CoverMapId cover : OrbicurveFiniteEtaleCoverMap cover cover) ≅
        𝟭 (S1764Fiber cover)) := by
  unfold S1764RawFiberFunctor S1641CoverMapId
  unfold OrbicurveFiniteEtaleCover.geometricFiberMap
  dsimp only
  refine ⟨CostructuredArrow.map₂IdIso _ _ _ ?_ ?_⟩
  · simp only [Pseudofunctor.StrongTrans.comp_app, eqToHom_refl, Category.id_comp]
    rfl
  · rfl

/-! ## 2. Exact missing hypotheses for the strict functor -/

/-- Exact finiteness input: the actual geometric fiber at S1726AffineOver/id
is finite for every finite-etale cover.  This is a Prop (using Finite, not the
data-carrying Fintype).  It is the geometric-fiber finiteness theorem of the
parallel S1735 task; it is not proved here. -/
def S1764FiberFiniteObligation : Prop :=
  ∀ cover : OrbicurveFiniteEtaleCover S1764Orbicurve,
    Finite (S1764Fiber cover)

/-- Exact factorization input: the raw geometric-fiber map is constant on
2-isomorphism classes of actual cover maps.  This is precisely the well-defined
descent of geometricFiberMap through the S1728 quotient category. -/
def S1764FiberMapWellDefinedObligation : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f g : OrbicurveFiniteEtaleCoverMap A B),
    S1728CoverMapRel f g →
      S1764RawFiberMap f = S1764RawFiberMap g

/-- Strict identity law for the canonical actual identity cover map. -/
def S1764RawIdentityObligation : Prop :=
  ∀ cover : OrbicurveFiniteEtaleCover S1764Orbicurve,
    S1764RawFiberMap
      (S1641CoverMapId cover : OrbicurveFiniteEtaleCoverMap cover cover) = id

/-- Strict composition law for the canonical actual composite cover maps. -/
def S1764RawCompositionObligation : Prop :=
  ∀ {A B C : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C),
    S1764RawFiberMap (S1641CoverMapComp f g) =
      S1764RawFiberMap g ∘ S1764RawFiberMap f

/-- The four exact strictification/finiteness inputs, bundled. -/
def S1764ConcreteFiberFunctorMissing : Prop :=
  S1764FiberFiniteObligation ∧
    S1764FiberMapWellDefinedObligation ∧
      S1764RawIdentityObligation ∧
        S1764RawCompositionObligation

/-! ## 3. Strict fiber data and its exactness -/

/-- A strict realization of the geometric-fiber assignment on the S1728
quotient category.  The field map is a genuine function on
2-isomorphism classes; map_mk says it is geometricFiberMap on every actual
representative; the last two fields are the strict functor laws. -/
structure S1764StrictFiberData where
  /-- Finiteness of every actual geometric fiber. -/
  finite : S1764FiberFiniteObligation
  /-- The function on S1728 hom-classes. -/
  map : ∀ {A B : OrbicurveFiniteEtaleCover S1764Orbicurve},
    S1728CoverMapClass A B → S1764Fiber A → S1764Fiber B
  /-- On a class represented by an actual cover map, the function is exactly
  geometricFiberMap of that map. -/
  map_mk : ∀ {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B),
    map (Quot.mk _ f) = S1764RawFiberMap f
  /-- Strict identity law. -/
  map_id : ∀ A : OrbicurveFiniteEtaleCover S1764Orbicurve,
    map (Quot.mk _ (S1641CoverMapId A)) = id
  /-- Strict composition law. -/
  map_comp : ∀ {A B C : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C),
    map (Quot.mk _ (S1641CoverMapComp f g)) =
      map (Quot.mk _ g) ∘ map (Quot.mk _ f)

/-- From the four exact obligations, build the strict fiber data.  The
function on quotient classes is Quot.lift of S1764RawFiberMap, made
well-defined by S1764FiberMapWellDefinedObligation. -/
noncomputable def S1764StrictFiberDataOfObligations
    (hF : S1764FiberFiniteObligation)
    (hW : S1764FiberMapWellDefinedObligation)
    (hId : S1764RawIdentityObligation)
    (hComp : S1764RawCompositionObligation) : S1764StrictFiberData where
  finite := hF
  map := fun {A B} q =>
    Quot.lift (fun f : OrbicurveFiniteEtaleCoverMap A B =>
        S1764RawFiberMap f)
      (fun f g h => hW f g h) q
  map_mk := by
    intro A B f
    rfl
  map_id := by
    intro A
    exact hId A
  map_comp := by
    intro A B C f g
    exact hComp f g

/-- Exactness: the strict fiber data exists if and only if the four named
obligations hold. -/
theorem S1764StrictFiberDataNonempty_iff :
    Nonempty S1764StrictFiberData ↔
      S1764ConcreteFiberFunctorMissing := by
  constructor
  · rintro ⟨D⟩
    refine ⟨D.finite, ?_, ?_, ?_⟩
    · intro A B f g h
      have hq : (Quot.mk _ f : S1728CoverMapClass A B) = Quot.mk _ g :=
        Quot.sound h
      calc
        S1764RawFiberMap f = D.map (Quot.mk _ f) := (D.map_mk f).symm
        _ = D.map (Quot.mk _ g) := by rw [hq]
        _ = S1764RawFiberMap g := D.map_mk g
    · intro cover
      calc
        S1764RawFiberMap
            (S1641CoverMapId cover) =
            D.map (Quot.mk _ (S1641CoverMapId cover)) :=
          (D.map_mk (S1641CoverMapId cover)).symm
        _ = id := D.map_id cover
    · intro A B C f g
      calc
        S1764RawFiberMap (S1641CoverMapComp f g) =
            D.map (Quot.mk _ (S1641CoverMapComp f g)) :=
          (D.map_mk (S1641CoverMapComp f g)).symm
        _ = D.map (Quot.mk _ g) ∘ D.map (Quot.mk _ f) :=
          D.map_comp f g
        _ = S1764RawFiberMap g ∘ S1764RawFiberMap f := by
          rw [D.map_mk f, D.map_mk g]
  · rintro ⟨hF, hW, hId, hComp⟩
    exact ⟨S1764StrictFiberDataOfObligations hF hW hId hComp⟩

/-! ## 4. Conditional construction of the actual functor to FintypeCat -/

/-- The actual geometric-fiber functor on the S1728 Category.{1,1}, landing in
FintypeCat.{0}.  Objects are the actual finite geometric fibers; on a
2-isomorphism class represented by an actual cover map f, the map is
geometricFiberMap f.  Conditional exactly on S1764StrictFiberData. -/
noncomputable def S1764FiberFunctorOfData
    (D : S1764StrictFiberData) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{0} := by
  letI : Category.{1, 1} (OrbicurveFiniteEtaleCover S1764Orbicurve) :=
    S1764ActualCategory
  exact
    { obj := fun cover =>
        letI : Finite (S1764Fiber cover) := D.finite cover
        FintypeCat.of (S1764Fiber cover)
      map := fun {A B} q =>
        letI : Finite (S1764Fiber A) := D.finite A
        letI : Finite (S1764Fiber B) := D.finite B
        FintypeCat.homMk (D.map q)
      map_id := by
        intro A
        apply FintypeCat.hom_ext
        intro x
        change D.map (Quot.mk _ (S1641CoverMapId A)) x = x
        rw [D.map_id A]
        rfl
      map_comp := by
        intro A B C f g
        induction f using Quot.inductionOn with
        | h f =>
          induction g using Quot.inductionOn with
          | h g =>
            apply FintypeCat.hom_ext
            intro x
            change D.map (Quot.mk _ (S1641CoverMapComp f g)) x =
              D.map (Quot.mk _ g) (D.map (Quot.mk _ f) x)
            rw [D.map_comp f g]
            rfl }

/-- The object map of the conditional functor is exactly the actual geometric
fiber. -/
@[simp] theorem S1764FiberFunctorOfData_obj
    (D : S1764StrictFiberData)
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    ((S1764FiberFunctorOfData D).obj cover).obj = S1764Fiber cover := rfl

/-- On a class represented by an actual cover map, the conditional functor's
map is FintypeCat.homMk of the raw geometric-fiber map. -/
theorem S1764FiberFunctorOfData_map_mk_apply
    (D : S1764StrictFiberData)
    {A B : OrbicurveFiniteEtaleCover S1764Orbicurve}
    (f : OrbicurveFiniteEtaleCoverMap A B) (x : S1764Fiber A) :
    (S1764FiberFunctorOfData D).map (Quot.mk _ f) x =
      S1764RawFiberMap f x := by
  change D.map (Quot.mk _ f) x = S1764RawFiberMap f x
  rw [D.map_mk f]

/-- The direct construction from the four exact obligations. -/
noncomputable def S1764FiberFunctorOfObligations
    (hF : S1764FiberFiniteObligation)
    (hW : S1764FiberMapWellDefinedObligation)
    (hId : S1764RawIdentityObligation)
    (hComp : S1764RawCompositionObligation) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{0} :=
  S1764FiberFunctorOfData
    (S1764StrictFiberDataOfObligations hF hW hId hComp)

/-- The same construction from the bundled missing proposition. -/
noncomputable def S1764FiberFunctorOfMissing
    (h : S1764ConcreteFiberFunctorMissing) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{0} :=
  S1764FiberFunctorOfObligations h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ## 5. The literal S1736 target universe: FintypeCat.{1}

The actual fiber is in Type 0.  The S1736 obligation at Category.{1,1} asks for
FintypeCat.{1}.  We lift the fiber by ULift.{1,0}; this is an equivalence of
finite types, not a replacement of the geometric fiber. -/

/-- The universe-lifted geometric-fiber functor, landing in the exact S1736
target universe FintypeCat.{1}. -/
noncomputable def S1764FiberFunctorULiftOfData
    (D : S1764StrictFiberData) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{1} := by
  letI : Category.{1, 1} (OrbicurveFiniteEtaleCover S1764Orbicurve) :=
    S1764ActualCategory
  exact
    { obj := fun cover =>
        letI : Finite (S1764Fiber cover) := D.finite cover
        letI : Finite (ULift.{1, 0} (S1764Fiber cover)) := inferInstance
        FintypeCat.of (ULift.{1, 0} (S1764Fiber cover))
      map := fun {A B} q =>
        FintypeCat.homMk
          (fun u : ULift.{1, 0} (S1764Fiber A) =>
            ULift.up (D.map q u.down))
      map_id := by
        intro A
        apply FintypeCat.hom_ext
        intro u
        change ULift.up (D.map (Quot.mk _ (S1641CoverMapId A)) u.down) = u
        rw [D.map_id A]
        cases u
        rfl
      map_comp := by
        intro A B C f g
        induction f using Quot.inductionOn with
        | h f =>
          induction g using Quot.inductionOn with
          | h g =>
            apply FintypeCat.hom_ext
            intro u
            change ULift.up (D.map (Quot.mk _ (S1641CoverMapComp f g)) u.down) =
              ULift.up (D.map (Quot.mk _ g) (D.map (Quot.mk _ f) u.down))
            rw [D.map_comp f g]
            rfl }

/-- The object map of the lifted functor is ULift of the actual geometric
fiber. -/
@[simp] theorem S1764FiberFunctorULiftOfData_obj
    (D : S1764StrictFiberData)
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    ((S1764FiberFunctorULiftOfData D).obj cover).obj =
      ULift.{1, 0} (S1764Fiber cover) := rfl

/-- The lifted construction from the four exact obligations. -/
noncomputable def S1764FiberFunctorULiftOfObligations
    (hF : S1764FiberFiniteObligation)
    (hW : S1764FiberMapWellDefinedObligation)
    (hId : S1764RawIdentityObligation)
    (hComp : S1764RawCompositionObligation) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{1} :=
  S1764FiberFunctorULiftOfData
    (S1764StrictFiberDataOfObligations hF hW hId hComp)

/-- The lifted construction from the bundled missing proposition. -/
noncomputable def S1764FiberFunctorULiftOfMissing
    (h : S1764ConcreteFiberFunctorMissing) :
    OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{1} :=
  S1764FiberFunctorULiftOfObligations h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ## 6. The exact residual of the S1736 fiber-functor obligation -/

/-- The exact remaining FiberFunctor class obligation for the concrete
lifted functor: the six preservation/reflection fields of Lenstra's fiber
functor.  This is a proposition; it is neither asserted nor derived from the
finiteness/factorization data. -/
def S1764FiberFunctorAxiomsObligation
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve)))
    (D : S1764StrictFiberData) : Prop :=
  Nonempty (@PreGaloisCategory.FiberFunctor
    (OrbicurveFiniteEtaleCover S1764Orbicurve)
    (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve))
    P (S1764FiberFunctorULiftOfData D))

/-- The exact residual in terms of the four concrete obligations. -/
def S1764FiberFunctorAxiomsObligationOfMissing
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve)))
    (h : S1764ConcreteFiberFunctorMissing) : Prop :=
  Nonempty (@PreGaloisCategory.FiberFunctor
    (OrbicurveFiniteEtaleCover S1764Orbicurve)
    (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve))
    P (S1764FiberFunctorULiftOfMissing h))

/-- Strict fiber data plus the six FiberFunctor fields gives the literal S1736
fiber-functor obligation.  This is a genuine conditional assembly: neither the
data nor the class is asserted. -/
theorem S1764S1736ActualFiberFunctorObligationOfData
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve)))
    (D : S1764StrictFiberData)
    (hAx : S1764FiberFunctorAxiomsObligation P D) :
    S1736ActualFiberFunctorObligation
      (F := S1764K) (X := S1764Orbicurve) P :=
  ⟨S1764FiberFunctorULiftOfData D, hAx⟩

/-- The same assembly from the four concrete obligations. -/
theorem S1764S1736ActualFiberFunctorObligationOfMissing
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve)))
    (h : S1764ConcreteFiberFunctorMissing)
    (hAx : S1764FiberFunctorAxiomsObligationOfMissing P h) :
    S1736ActualFiberFunctorObligation
      (F := S1764K) (X := S1764Orbicurve) P :=
  ⟨S1764FiberFunctorULiftOfMissing h, hAx⟩

/-- The exact unresolved part of the S1736 obligation, recorded without
asserting an inhabitant: strict fiber data (equivalently the four concrete
obligations) together with the six FiberFunctor fields. -/
def S1764ExactMissing
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve))) : Prop :=
  ∃ D : S1764StrictFiberData, S1764FiberFunctorAxiomsObligation P D

/-- ExactMissing is equivalent to the four named obligations plus the six
FiberFunctor fields for some strict realization. -/
theorem S1764ExactMissing_iff
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve)
      (S1736ActualCategory (F := S1764K) (X := S1764Orbicurve))) :
    S1764ExactMissing P ↔
      S1764ConcreteFiberFunctorMissing ∧
        ∃ D : S1764StrictFiberData,
          S1764FiberFunctorAxiomsObligation P D := by
  constructor
  · rintro ⟨D, hAx⟩
    exact ⟨S1764StrictFiberDataNonempty_iff.mp ⟨D⟩, D, hAx⟩
  · rintro ⟨_, D, hAx⟩
    exact ⟨D, hAx⟩

/-! ## 7. Status summary

Unconditional:
* the actual base point S1764BasePoint at S1726AffineOver/id;
* the actual fiber type S1764Fiber cover (Type 0);
* the raw geometric-fiber functors S1764RawFiberFunctor and object functions
  S1764RawFiberMap, literally geometricFiberMap;
* the identity natural isomorphism S1764RawFiberFunctor_id_natIso.

Conditional:
* S1764FiberFunctorOfData / S1764FiberFunctorOfMissing to FintypeCat.{0};
* S1764FiberFunctorULiftOfData / ...ULiftOfMissing to FintypeCat.{1};
* S1764S1736ActualFiberFunctorObligationOfData / ...OfMissing.

Missing:
* S1764FiberFiniteObligation (actual geometric-fiber finiteness; S1735);
* S1764FiberMapWellDefinedObligation (strict descent through the S1728
  2-isomorphism quotient);
* S1764RawIdentityObligation, S1764RawCompositionObligation (strict
  pseudofunctor coherences);
* the six FiberFunctor fields (S1764FiberFunctorAxiomsObligation).

No sorry, no axiom, no fake fiber. -/

/-! ## 8. Axiom audit and interface checks -/

#print axioms S1764RawFiberFunctor_id_natIso
#print axioms S1764StrictFiberDataNonempty_iff
#print axioms S1764FiberFunctorOfData_obj
#print axioms S1764FiberFunctorOfData_map_mk_apply
#print axioms S1764FiberFunctorULiftOfData_obj
#print axioms S1764S1736ActualFiberFunctorObligationOfData
#print axioms S1764S1736ActualFiberFunctorObligationOfMissing
#print axioms S1764ExactMissing_iff

#check S1764K
#check S1764Orbicurve
#check S1764BaseScheme
#check S1764BasePoint
#check S1764Fiber
#check S1764ActualCategory
#check S1764ActualCategory_eq
#check S1764RawFiberFunctor
#check S1764RawFiberMap
#check S1764RawFiberFunctor_id_natIso
#check S1764FiberFiniteObligation
#check S1764FiberMapWellDefinedObligation
#check S1764RawIdentityObligation
#check S1764RawCompositionObligation
#check S1764ConcreteFiberFunctorMissing
#check S1764StrictFiberData
#check S1764StrictFiberDataOfObligations
#check S1764StrictFiberDataNonempty_iff
#check S1764FiberFunctorOfData
#check S1764FiberFunctorOfData_obj
#check S1764FiberFunctorOfData_map_mk_apply
#check S1764FiberFunctorOfObligations
#check S1764FiberFunctorOfMissing
#check S1764FiberFunctorULiftOfData
#check S1764FiberFunctorULiftOfData_obj
#check S1764FiberFunctorULiftOfObligations
#check S1764FiberFunctorULiftOfMissing
#check S1764FiberFunctorAxiomsObligation
#check S1764FiberFunctorAxiomsObligationOfMissing
#check S1764S1736ActualFiberFunctorObligationOfData
#check S1764S1736ActualFiberFunctorObligationOfMissing
#check S1764ExactMissing
#check S1764ExactMissing_iff

end LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
