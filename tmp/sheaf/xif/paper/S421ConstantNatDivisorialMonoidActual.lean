import tmp.sheaf.xif.paper.S423NatDivisorialAddMonoidActual
import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual
/-! # S421: constant ℕ divisor monoid, and the D_v^⊢ universe gap
The generic constant-ℕ DivisorialMonoidOn is constructed on any small base
category D : Type u with [Category.{u} D].  For the actual
DvTriangleFieldCover K the object type is Type (u+1) and the available
category has Category.{u, u+1}, so it cannot be fed to the current
DivisorialMonoidOn (which asks Category.{u} D, i.e. objects and homs in the
same universe u).  The exact small-model instance requirement is recorded; no
universe coercion or fake instance is asserted. -/
noncomputable section
open CategoryTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S421ConstantNatDivisorialMonoidActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open LeanFormal.IUT.XiFPaper.S423NatDivisorialAddMonoidActual
universe u v
/-- Constant ℕ divisorial monoid on any small base category. -/
noncomputable def constantNatDivisorialMonoidOn
    (D : Type) [Category D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop) :
    Iut.DivisorialMonoidOn D IsFSM where
  obj _ := natDivisorialAddMonoid
  pullback _ := AddMonoidHom.id ℕ
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id
/-- Actual finite-étale field-cover base; its object type is Type (u+1). -/
abbrev DvBase (K : Type u) [Field K] : Type (u + 1) :=
  DvTriangleFieldCover K
/-- The available category has small homs but large objects. -/
noncomputable instance dvBaseCategorySmallHom (K : Type u) [Field K] :
    Category.{u, u + 1} (DvBase K) := inferInstance
/-- Exact missing small-model category instance: same objects, all homs lifted
to Type (u+1), so that the current DivisorialMonoidOn universe discipline
applies.  No such instance is constructed here. -/
def DvSmallModelCategoryRequired (K : Type u) [Field K] : Prop :=
  Nonempty (Category.{u + 1, u + 1} (DvBase K))
end LeanFormal.IUT.XiFPaper.S421ConstantNatDivisorialMonoidActual
