import tmp.sheaf.xif.paper.S432SmallModelActual
import tmp.sheaf.xif.paper.S451GroupLikePullbackAuditActual
import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual

/-! # S462: Example32 phi/IsFSM=IsIso and rational-function inclusion pullback -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S462Example32PhiIsoGroupLikeActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open LeanFormal.IUT.XiFPaper.S451GroupLikePullbackAuditActual
open Iut.SourceModelFrobenioid
open scoped BigOperators

universe u

variable (K : Type u) [Field K]

/-- IsFSM = IsIso on the size-aligned base. -/
def Example32FSMIso : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop :=
  fun {_ _} f => IsIso f

/-- Constant N divisor monoid with IsFSM = IsIso.  Identity pullback is
bijective on every arrow, hence in particular on IsFSM arrows. -/
noncomputable def example32PhiIso :
    DivisorialMonoidOn.{u + 1} (Example32SmallBase K)
      (Example32FSMIso (K := K)) where
  obj _ := Iut.SourceFinitePlaceReconstruction.stageDivisorialAddMonoid.{u + 1}
  pullback _ := AddMonoidHom.id _
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

/-- The actual field at a size-aligned cover object. -/
abbrev Example32CoverField (X : Example32SmallBase K) : Type u :=
  X.objDown.unop.obj.obj

noncomputable instance example32CoverFieldField (X : Example32SmallBase K) :
    Field (Example32CoverField K X) :=
  (X.objDown.unop.property).toField

/-- The underlying algebra map of an opposite-category arrow. -/
noncomputable def coverAlgHom {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    Example32CoverField K Y →ₐ[K] Example32CoverField K X :=
  f.down.unop.hom.hom.hom

/-- Inclusion pullback of rational-function units along an opposite-category
algebra map. -/
noncomputable def example32RationalPullback
    {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    Additive (Example32CoverField K Y)ˣ →+
      Additive (Example32CoverField K X)ˣ :=
  (Units.map (f.down.unop.hom.hom.hom.toRingHom.toMonoidHom)).toAdditive

theorem example32RationalPullback_injective
    {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    Function.Injective (example32RationalPullback (K := K) f) := by
  intro x y hxy
  apply Additive.toMul.injective
  exact unitsMap_injective
    ((f.down.unop.hom.hom.hom).toRingHom.toMonoidHom)
    (f.down.unop.hom.hom.hom).injective
    (congrArg Additive.toMul hxy)

theorem example32RationalPullback_bijective_of_isIso
    {X Y : Example32SmallBase K} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (example32RationalPullback (K := K) f) := by
  refine ⟨example32RationalPullback_injective (K := K) f, ?_⟩
  intro y
  let g : Y ⟶ X := inv f
  have hcomp : coverAlgHom (K := K) (f ≫ g) =
      (coverAlgHom (K := K) f).comp (coverAlgHom (K := K) g) := rfl
  have hid : coverAlgHom (K := K) (𝟙 X) = AlgHom.id K (Example32CoverField K X) := rfl
  have h : (coverAlgHom (K := K) f).comp (coverAlgHom (K := K) g) =
      AlgHom.id K (Example32CoverField K X) := by
    rw [← hcomp, ← hid, IsIso.hom_inv_id]
  refine ⟨example32RationalPullback (K := K) g y, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  have hy : (coverAlgHom (K := K) f) ((coverAlgHom (K := K) g)
      (Additive.toMul y).val) = (Additive.toMul y).val := by
    simpa using congrArg
      (fun e : Example32CoverField K X →ₐ[K] Example32CoverField K X =>
        e (Additive.toMul y).val) h
  simpa [example32RationalPullback, coverAlgHom] using hy

end LeanFormal.IUT.XiFPaper.S462Example32PhiIsoGroupLikeActual

end
