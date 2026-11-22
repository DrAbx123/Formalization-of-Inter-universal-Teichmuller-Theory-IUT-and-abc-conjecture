/-
# S1796: universe alignment of the Orbit fiber field

## Question

S1764 found that the actual geometric fiber

  S1764Fiber cover = OrbicurveFiniteEtaleCover.GeometricFiber
    S1764BaseScheme S1764BasePoint cover

lives in `Type 0`, while the auxiliary obligation
`S1736ActualFiberFunctorObligation` for the S1728 `Category.{1,1}` asks for
`FintypeCat.{1}` and therefore needs `ULift.{1,0}`.  S1736 also records that the
literal target field of `Iut.OrbicurveEtaleFundamentalGroup` at `F : Type u` is

  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X)
  fiber         : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}.

For the actual D6 orbicurve `F = S1726K : Type 0` the literal target therefore
has `Category.{0,1}` and `FintypeCat.{0}`, whereas the S1728 actual category is
`Category.{1,1}`.

## Answer checked in this file

* The actual fiber is a Type-0 type: `S1796FiberType` has type `Type`.
* At `FintypeCat.{0}` the geometric fiber can be used directly, with no
  universe lift: `S1796FiberObject0` and `S1796FiberObject0_direct`.
* The literal target's fiber field really has object carriers in `Type 0`:
  `S1796TargetFiberCarrier` is a function into `Type`; its identification
  field is an equivalence to the literal geometric fiber of the target base
  point (`S1796TargetFiberIdentification`).
* At `Category.{0,1}` any `GaloisCategory` forces the fiber functor to land in
  `FintypeCat.{0}`; at `Category.{1,1}` it forces `FintypeCat.{1}`
  (`S1796GaloisFiberUniverse01`, `S1796GaloisFiberUniverse11`).
* The S1736 actual fiber-functor obligation is definitionally the existential
  at `FintypeCat.{1}` (`S1796S1736ActualFiberFunctorObligation_eq`).

Consequently the no-`ULift` version is the literal target universe

  `Category.{0,1}` on the cover type, `fiber : C ⥤ FintypeCat.{0}`,

which is exactly what `OrbicurveEtaleFundamentalGroup` stores at `F : Type 0`.
The `ULift` in S1764 is forced only by the different target universe
`FintypeCat.{1}` used in `S1736ActualFiberFunctorObligation` for the
`Category.{1,1}` actual S1728 category.  It is a target-universe mismatch, not a
property of the geometric fiber.

## Exact universe obstruction at `FintypeCat.{1}`

`FintypeCat.{1}` objects have carriers in `Type 1`, while `S1796Fiber cover` is
in `Type 0`.  Lean universes are not cumulative, and heterogeneous equality is
same-universe in Lean 4

  `@HEq : {α : Sort u} → α → {β : Sort u} → β → Prop`,

so the direct object assignment `cover ↦ FintypeCat.of (S1796Fiber cover)` is
not merely unprovable at `FintypeCat.{1}`: it is ill-typed.  The file records
this by the kernel-checked `#check_failure` certificate below.  The only
target-universe-correct choices are (a) `FintypeCat.{0}` (the literal target)
or (b) `FintypeCat.{1}` with a lifted object type, which is no longer the
geometric fiber itself.

The functor-level strictification at `Category.{0,1}` (well-definedness on the
2-isomorphism quotient, identity/composition laws, finiteness) is exactly the
S1764 `S1764StrictFiberData` content; it is not a universe obstruction.  This
file proves the universe alignment and the direct object assignment; it does
not rebuild the strict functor.

No `ULift`-valued replacement and no lifted functor is constructed here; the
file only discusses the target universe, as requested.
-/

import tmp.sheaf.xif.paper.S1764ActualFiberFunctorActual
import Mathlib.CategoryTheory.FintypeCat

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.defProp false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1796FiberUniverseActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

/-! ## 1. The actual fiber is a Type-0 type -/

/-- The actual geometric fiber of S1764, at the actual base point
`S1726AffineOver/id`. -/
abbrev S1796Fiber (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) : Type :=
  S1764Fiber cover

/-- Certificate that the actual fiber is a `Type` (universe 0), not a `Type 1`.
The declaration would not elaborate if `S1796Fiber cover` were `Type 1`. -/
noncomputable def S1796FiberType
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) : Type :=
  S1796Fiber cover

/-- A finite actual fiber, packaged directly as an object of `FintypeCat.{0}`.
No `ULift` occurs. -/
noncomputable def S1796FiberObject0
    (h : ∀ cover, Finite (S1796Fiber cover))
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) : FintypeCat.{0} :=
  letI := h cover
  FintypeCat.of (S1796Fiber cover)

/-- The object map of `S1796FiberObject0` is exactly the geometric fiber. -/
@[simp] theorem S1796FiberObject0_obj
    (h : ∀ cover, Finite (S1796Fiber cover))
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    (S1796FiberObject0 h cover).obj = S1796Fiber cover := rfl

/-- At the literal target universe `FintypeCat.{0}`, the geometric fiber can be
used directly as the object assignment; no universe lift is needed. -/
theorem S1796FiberObject0_direct
    (h : ∀ cover, Finite (S1796Fiber cover)) :
    ∃ G : OrbicurveFiniteEtaleCover S1764Orbicurve → FintypeCat.{0},
      ∀ cover, (G cover).obj = S1796Fiber cover :=
  ⟨S1796FiberObject0 h, S1796FiberObject0_obj h⟩

/-! ## 2. The literal target field is already at `FintypeCat.{0}` -/

/-- The carrier of the literal target's fiber object is a `Type` (universe 0).
This is the field `fiber : C ⥤ FintypeCat.{0}` of
`OrbicurveEtaleFundamentalGroup` at `F : Type 0`, read on objects. -/
noncomputable def S1796TargetFiberCarrier
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup (F := S1764K) S1764Orbicurve G)
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) : Type := by
  letI := D.coverCategory
  exact (D.fiber.obj cover).obj

/-- The target's `fiberIdentification` is an equivalence of Type-0 types to the
literal geometric fiber at the target's own base point. -/
noncomputable def S1796TargetFiberIdentification {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup (F := S1764K) S1764Orbicurve G)
    (cover : OrbicurveFiniteEtaleCover S1764Orbicurve) :
    S1796TargetFiberCarrier D cover ≃
      OrbicurveFiniteEtaleCover.GeometricFiber
        D.baseScheme D.basePoint cover := by
  letI := D.coverCategory
  exact D.fiberIdentification cover

/-! ## 3. `GaloisCategory` fixes the fiber target universe

At `Category.{0,1}` the class stores a fiber functor to `FintypeCat.{0}`; at
`Category.{1,1}` it stores one to `FintypeCat.{1}`.  These are the two target
universes compared in the question. -/

/-- `GaloisCategory` at `Category.{0,1}` forces the fiber target
`FintypeCat.{0}`. -/
theorem S1796GaloisFiberUniverse01
    (C : Type 1) [Category.{0, 1} C] (h : GaloisCategory C) :
    ∃ F : C ⥤ FintypeCat.{0},
      Nonempty (PreGaloisCategory.FiberFunctor F) :=
  h.hasFiberFunctor

/-- `GaloisCategory` at `Category.{1,1}` forces the fiber target
`FintypeCat.{1}`. -/
theorem S1796GaloisFiberUniverse11
    (C : Type 1) [Category.{1, 1} C] (h : GaloisCategory C) :
    ∃ F : C ⥤ FintypeCat.{1},
      Nonempty (PreGaloisCategory.FiberFunctor F) :=
  h.hasFiberFunctor

/-! ## 4. The S1736 actual obligation is at `FintypeCat.{1}` -/

/-- The S1736 actual fiber-functor obligation is definitionally the existential
with target `FintypeCat.{1}`.  This is the obligation which S1764 lifts into;
it is not the literal `OrbicurveEtaleFundamentalGroup.fiber` field at `u = 0`,
whose target is `FintypeCat.{0}`. -/
theorem S1796S1736ActualFiberFunctorObligation_eq
    (P : @PreGaloisCategory.{1, 1}
      (OrbicurveFiniteEtaleCover S1764Orbicurve) S1764ActualCategory) :
    S1736ActualFiberFunctorObligation
        (F := S1764K) (X := S1764Orbicurve) P =
      (∃ Fib : OrbicurveFiniteEtaleCover S1764Orbicurve ⥤ FintypeCat.{1},
        Nonempty (@PreGaloisCategory.FiberFunctor
          (OrbicurveFiniteEtaleCover S1764Orbicurve)
          S1764ActualCategory P Fib)) := rfl

/-! ## 5. The exact universe obstruction at `FintypeCat.{1}` -/

/- The direct object assignment at universe 1 is ill-typed: `FintypeCat.{1}`
expects a `Type 1` carrier, but the actual fiber is a `Type 0` type.  This
`#check_failure` is a kernel-checked certificate that no direct (unlifted)
object assignment exists at `FintypeCat.{1}`; it is the precise form of the
universe obstruction. -/
section
variable (h : ∀ cover, Finite (S1796Fiber cover))
#check_failure (fun cover : OrbicurveFiniteEtaleCover S1764Orbicurve =>
    (letI := h cover;
      (FintypeCat.of (S1796Fiber cover) : FintypeCat.{1})))
end

/-! ## 6. Interface checks and axiom audit -/

#check S1796Fiber
#check S1796FiberType
#check S1796FiberObject0
#check S1796FiberObject0_obj
#check S1796FiberObject0_direct
#check S1796TargetFiberCarrier
#check S1796TargetFiberIdentification
#check S1796GaloisFiberUniverse01
#check S1796GaloisFiberUniverse11
#check S1796S1736ActualFiberFunctorObligation_eq

#print axioms S1796FiberObject0_obj
#print axioms S1796FiberObject0_direct
#print axioms S1796TargetFiberIdentification
#print axioms S1796GaloisFiberUniverse01
#print axioms S1796GaloisFiberUniverse11
#print axioms S1796S1736ActualFiberFunctorObligation_eq

end LeanFormal.IUT.XiFPaper.S1796FiberUniverseActual
