import tmp.sheaf.xif.paper.S456RationalInclusionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

theorem arrowAlgebraMap_id_local (X : Example32SmallBase K) :
    arrowAlgebraMap (𝟙 X) = AlgHom.id K (coverField X) := by
  ext x
  rfl

theorem arrowAlgebraMap_comp_local {X Y Z : Example32SmallBase K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    arrowAlgebraMap (f ≫ g) =
      (arrowAlgebraMap f).comp (arrowAlgebraMap g) := by
  ext x
  rfl

noncomputable def uliftUnitMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    ULift.{u+1} (coverField Y)ˣ →* ULift.{u+1} (coverField X)ˣ where
  toFun x := ULift.up ((unitInclusionPullback f) x.down)
  map_one' := by
    apply ULift.ext
    simp [unitInclusionPullback]
  map_mul' a b := by
    apply ULift.ext
    simp [unitInclusionPullback]

noncomputable def example32RationalFunctionsLiftedULift :
    GroupLikeAddMonoidOn (Example32SmallBase K) (Example32IsFSM (K := K)) where
  obj X := Additive (ULift.{u+1} (coverField X)ˣ)
  addCommGroup X := inferInstance
  pullback f := (uliftUnitMap f).toAdditive
  pullback_id X := by
    ext x
    change arrowAlgebraMap (𝟙 X) x.down = x.down
    rw [arrowAlgebraMap_id_local]
    rfl
  pullback_comp f g := by
    ext x
    change arrowAlgebraMap (f ≫ g) x.down =
      arrowAlgebraMap f (arrowAlgebraMap g x.down)
    rw [arrowAlgebraMap_comp_local]
    rfl
  pullback_injective f := by
    intro x y h
    change (uliftUnitMap f) x = (uliftUnitMap f) y at h
    apply ULift.ext
    apply unitInclusionPullback_injective f
    simpa [uliftUnitMap] using congrArg ULift.down h
  fsmPullbackIsIso := by
    intro X Y f hf
    constructor
    · intro x y h
      change (uliftUnitMap f) x = (uliftUnitMap f) y at h
      apply ULift.ext
      apply unitInclusionPullback_injective f
      simpa [uliftUnitMap] using congrArg ULift.down h
    · intro y
      obtain ⟨x, hx⟩ := hf.surjective y.toMul.down
      refine ⟨Additive.ofMul (ULift.up x), ?_⟩
      change (uliftUnitMap f) (ULift.up x) = y
      apply ULift.ext
      exact hx

end LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual

end
