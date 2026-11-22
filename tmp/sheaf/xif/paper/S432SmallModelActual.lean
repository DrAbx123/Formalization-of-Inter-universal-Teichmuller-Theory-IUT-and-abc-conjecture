import tmp.sheaf.xif.paper.S409Example32FrobenioidActual
import Mathlib.CategoryTheory.Category.ULift
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# S432: size-aligned model for the field-cover base

`DvTriangleFieldCover K` has objects in `Type (u+1)` and homs in `Type u`,
so its category instance is `Category.{u, u+1}` and cannot instantiate
`DivisorialMonoidOn`, which requires the same universe for objects and homs.

`ULiftHom.{u+1}` keeps the objects (hence the object semantics) and lifts the
hom types, producing a category with universe `{u+1, u+1}` on the same objects.
This is a size alignment, not a fake small carrier; it is equivalent to the
original category via `ULiftHom.equiv`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S432SmallModelActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Iut.SourceModelFrobenioid

universe u

variable (K : Type u) [Field K]

/-- Original paper-oriented base (object universe `u+1`, hom universe `u`). -/
abbrev Example32Base : Type (u + 1) :=
  (DvTriangleFieldCover K)ᵒᵖ

/-- Size-aligned base: same objects, hom types lifted to Type (u+1). -/
abbrev Example32SmallBase : Type (u + 1) :=
  ULiftHom.{u + 1} (Example32Base K)

/-- The size-aligned base is equivalent to the original category. -/
noncomputable def example32SmallBaseEquiv :
    Example32Base K ≌ Example32SmallBase K :=
  ULiftHom.equiv

/-- The constant `N` divisor monoid on the size-aligned base. -/
noncomputable def example32Phi :
    DivisorialMonoidOn.{u + 1} (Example32SmallBase K)
      (fun {_ _} _ => True) where
  obj _ := Iut.SourceFinitePlaceReconstruction.stageDivisorialAddMonoid.{u + 1}
  pullback _ := AddMonoidHom.id _
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

/-- Exact missing rational functions/Input on the size-aligned base. -/
abbrev Example32SmallInput (K : Type u) [Field K] : Type _ :=
  Input (example32Phi K)

def Example32SmallInputRequired : Prop :=
  Nonempty (Example32SmallInput K)

/-- Actual category instance at universe `u+1` on the size-aligned base. -/
@[reducible] noncomputable def example32SmallBaseCategory :
    Category.{u + 1} (Example32SmallBase K) :=
  inferInstance

/-- Conditional actual FrobenioidPresentation on the size-aligned base, from
the still-missing Input datum plus connected/totally-epimorphic hypotheses. -/
noncomputable def example32SmallFrobenioidPresentation
    (data : Example32SmallInput K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := example32Phi K) (data := data) baseTotallyEpimorphic

end LeanFormal.IUT.XiFPaper.S432SmallModelActual
end
