import Iut.Foundations.SourceModelFrobenioid
import Mathlib.RingTheory.SimpleRing.Basic
/-! # S460: GroupLikeAddMonoidOn rational functions by function-field inclusion
For a contravariant field-cover model (D^op direction), rationalFunctions.obj X
is Additive (L_X)^× and pullback is the algebraMap/inclusion L_Y -> L_X.
The FSM class is IsFSM f := IsIso f, not True; this is exactly the condition
under which the inclusion pullback is an isomorphism.  Norm is not used. -/
noncomputable section
open CategoryTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S460RationalFunctionsFieldCoverActual
open Iut
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
variable (D : Type u) [Category.{u} D]
variable (L : D → Type u)
variable [∀ X, Field (L X)]
variable [∀ X, Algebra K (L X)]
-- Contravariant function-field inclusion: for f : X -> Y, an algebra map
-- L Y -> L X.
variable (pull : ∀ {X Y : D}, (X ⟶ Y) → L Y →ₐ[K] L X)
variable (pull_id : ∀ X : D, pull (𝟙 X) = AlgHom.id K (L X))
variable (pull_comp : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull (f ≫ g) = (pull f).comp (pull g))
/-- Field algebra maps are injective. -/
theorem pull_injective {X Y : D} (f : X ⟶ Y) :
    Function.Injective (pull f) :=
  RingHom.injective (pull f).toRingHom
/-- Rational functions as an additive group-like monoid: obj = Additive L^×,
pullback = Units.map of the function-field inclusion. -/
noncomputable def rationalFunctions :
    GroupLikeAddMonoidOn D (fun f => IsIso f) where
  obj X := Additive (L X)ˣ
  addCommGroup X := inferInstance
  pullback f := (Units.map (pull f).toMonoidHom).toAdditive
  pullback_id X := by
    ext x
    simp [pull_id]
  pullback_comp f g := by
    ext x
    simp [pull_comp, MonoidHom.comp_apply, Units.map]
  pullback_injective {X Y} f := by
    intro x y hxy
    have hxy' : Additive.toMul ((Units.map (pull f).toMonoidHom).toAdditive x) = Additive.toMul ((Units.map (pull f).toMonoidHom).toAdditive y) :=
      congrArg Additive.toMul hxy
    have hfield : (pull f) (((Additive.toMul x : (L Y)ˣ) : L Y)) =
        (pull f) (((Additive.toMul y : (L Y)ˣ) : L Y)) := by
      simpa [Units.map] using congrArg Units.val hxy'
    have hinj : Function.Injective (pull f) := RingHom.injective (pull f).toRingHom
    have hu : (Additive.toMul x : (L Y)ˣ) = Additive.toMul y := by
      apply Units.ext
      exact hinj hfield
    exact (Additive.toMul (α := (L Y)ˣ)).injective hu

  fsmPullbackIsIso {X Y} f hf := by
    letI : IsIso f := hf
    have h1 : (pull f).comp (pull (CategoryTheory.inv f)) = AlgHom.id K (L X) := by
      rw [← pull_comp]
      simp [pull_id]
    have h2 : (pull (CategoryTheory.inv f)).comp (pull f) = AlgHom.id K (L Y) := by
      rw [← pull_comp]
      simp [pull_id]
    have hbij : Function.Bijective (pull f) := by
      constructor
      · intro a b hab
        have ha2 := congrFun (congrArg DFunLike.coe h2) a
        have hb2 := congrFun (congrArg DFunLike.coe h2) b
        calc
          a = pull (CategoryTheory.inv f) (pull f a) := ha2.symm
          _ = pull (CategoryTheory.inv f) (pull f b) := congrArg _ hab
          _ = b := hb2
      · intro y
        refine ⟨pull (CategoryTheory.inv f) y, ?_⟩
        have h1y := congrFun (congrArg DFunLike.coe h1) y
        simpa [AlgHom.comp_apply] using h1y
    constructor
    · intro x y hxy
      have hxy' : Additive.toMul ((Units.map (pull f).toMonoidHom).toAdditive x) = Additive.toMul ((Units.map (pull f).toMonoidHom).toAdditive y) :=
        congrArg Additive.toMul hxy
      have hfield : (pull f) (((Additive.toMul x : (L Y)ˣ) : L Y)) =
          (pull f) (((Additive.toMul y : (L Y)ˣ) : L Y)) := by
        simpa [Units.map] using congrArg Units.val hxy'
      have hu : (Additive.toMul x : (L Y)ˣ) = Additive.toMul y := by
        apply Units.ext
        exact hbij.1 hfield
      exact (Additive.toMul (α := (L Y)ˣ)).injective hu
    · intro y
      let w : (L X)ˣ := Additive.toMul y
      let u : (L Y)ˣ := Units.map (pull (CategoryTheory.inv f)).toMonoidHom w
      refine ⟨Additive.ofMul u, ?_⟩
      have h : Units.map (pull f).toMonoidHom u = w := by
        apply Units.ext
        change (pull f) (u : L Y) = (w : L X)
        have h1w := congrFun (congrArg DFunLike.coe h1) (w : L X)
        simpa [u, AlgHom.comp_apply] using h1w
      change Additive.ofMul (Units.map (pull f).toMonoidHom u) = y
      rw [h]
      change Additive.ofMul w = y
      simp [w]
end LeanFormal.IUT.XiFPaper.S460RationalFunctionsFieldCoverActual
