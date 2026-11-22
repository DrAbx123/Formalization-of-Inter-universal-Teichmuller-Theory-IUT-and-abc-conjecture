import tmp.sheaf.xif.paper.S469RationalFunctionsLiftedActual
import tmp.sheaf.xif.paper.S456RationalInclusionActual
/-! # S474: S469 rational functions with IsFSM := IsIso
Reuse the actual ULift carrier/pullback from S469; only the FSM class is
changed to IsIso, using arrowAlgebraMap_comp' to prove that an isomorphism
gives a bijective unit inclusion. -/
noncomputable section
open CategoryTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
theorem arrowAlgebraMap_id' (X : Example32SmallBase K) :
    arrowAlgebraMap (K := K) (𝟙 X) = AlgHom.id K (coverField (K := K) X) := by
  ext x
  rfl
theorem arrowAlgebraMap_comp' {X Y Z : Example32SmallBase K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    arrowAlgebraMap (K := K) (f ≫ g) =
      (arrowAlgebraMap (K := K) f).comp (arrowAlgebraMap (K := K) g) := by
  ext x
  rfl
def Example32FSMIso : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop := fun {_ _} f => IsIso f
theorem arrowAlgebraMap_bijective_of_isIso {X Y : Example32SmallBase K}
    (f : X ⟶ Y) [IsIso f] : Function.Bijective (arrowAlgebraMap (K := K) f) := by
  have h1 : (arrowAlgebraMap (K := K) f).comp (arrowAlgebraMap (K := K) (CategoryTheory.inv f)) =
      AlgHom.id K (coverField (K := K) X) := by
    rw [← arrowAlgebraMap_comp']
    simpa using arrowAlgebraMap_id' (K := K) X
  have h2 : (arrowAlgebraMap (K := K) (CategoryTheory.inv f)).comp (arrowAlgebraMap (K := K) f) =
      AlgHom.id K (coverField (K := K) Y) := by
    rw [← arrowAlgebraMap_comp']
    simpa using arrowAlgebraMap_id' (K := K) Y
  constructor
  · intro a b hab
    have ha2 := congrFun (congrArg DFunLike.coe h2) a
    have hb2 := congrFun (congrArg DFunLike.coe h2) b
    calc
      a = arrowAlgebraMap (K := K) (CategoryTheory.inv f) (arrowAlgebraMap (K := K) f a) := ha2.symm
      _ = arrowAlgebraMap (K := K) (CategoryTheory.inv f) (arrowAlgebraMap (K := K) f b) :=
        congrArg _ hab
      _ = b := hb2
  · intro y
    refine ⟨arrowAlgebraMap (K := K) (CategoryTheory.inv f) y, ?_⟩
    have hcomp : (arrowAlgebraMap (K := K) f).comp
        (arrowAlgebraMap (K := K) (CategoryTheory.inv f)) =
        AlgHom.id K (coverField (K := K) X) := by
      rw [← arrowAlgebraMap_comp']
      simpa using arrowAlgebraMap_id' (K := K) X
    have h1y := congrFun (congrArg DFunLike.coe hcomp) (y : coverField (K := K) X)
    simpa [AlgHom.comp_apply] using h1y
theorem unitInclusionPullback_bijective_of_isIso {X Y : Example32SmallBase K}
    (f : X ⟶ Y) [IsIso f] : Function.Bijective (unitInclusionPullback (K := K) f) := by
  have hbij := arrowAlgebraMap_bijective_of_isIso (K := K) f
  constructor
  · intro x y hxy
    apply Units.ext
    apply hbij.1
    exact congrArg Units.val hxy
  · intro y
    let ux : (coverField (K := K) Y)ˣ :=
      Units.map (arrowAlgebraMap (K := K) (CategoryTheory.inv f)).toMonoidHom y
    refine ⟨ux, ?_⟩
    apply Units.ext
    change arrowAlgebraMap (K := K) f (ux : coverField (K := K) Y) =
      (y : coverField (K := K) X)
    have hcomp : (arrowAlgebraMap (K := K) f).comp
        (arrowAlgebraMap (K := K) (CategoryTheory.inv f)) =
        AlgHom.id K (coverField (K := K) X) := by
      rw [← arrowAlgebraMap_comp']
      simpa using arrowAlgebraMap_id' (K := K) X
    have h1y := congrFun (congrArg DFunLike.coe hcomp) (y : coverField (K := K) X)
    simpa [ux, AlgHom.comp_apply, unitInclusionPullback, Units.map] using h1y

/-- Actual GroupLikeAddMonoidOn on S432 small base with IsFSM := IsIso. -/
noncomputable def example32RationalFunctionsIso :
    GroupLikeAddMonoidOn (Example32SmallBase K) (Example32FSMIso (K := K)) where
  obj X := Additive (ULift.{u+1} (coverField (K := K) X)ˣ)
  addCommGroup X := inferInstance
  pullback f := (uliftUnitMap (K := K) f).toAdditive
  pullback_id X := (example32RationalFunctionsLiftedULift (K := K)).pullback_id X
  pullback_comp f g := (example32RationalFunctionsLiftedULift (K := K)).pullback_comp f g
  pullback_injective f := (example32RationalFunctionsLiftedULift (K := K)).pullback_injective f
  fsmPullbackIsIso {X Y} f hf := by
    letI : IsIso f := hf
    exact (example32RationalFunctionsLiftedULift (K := K)).fsmPullbackIsIso f
      (unitInclusionPullback_bijective_of_isIso (K := K) f)
end LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
