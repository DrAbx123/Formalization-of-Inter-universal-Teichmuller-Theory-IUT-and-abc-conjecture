import tmp.sheaf.xif.paper.S480Example32InputActual
import tmp.sheaf.xif.paper.S465LiftedDivisorMapActual
import tmp.sheaf.xif.paper.S469RationalFunctionsLiftedActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open Additive

universe u
variable (K : Type u) [Field K]

noncomputable def stageDivisorULiftEquiv' :
    StageDivisor.{u} ≃+ StageDivisor.{u+1} :=
  (stageDivisorEquivNat : StageDivisor.{u} ≃+ ℕ).trans
    (stageDivisorEquivNat : StageDivisor.{u+1} ≃+ ℕ).symm

noncomputable def grothendieckStageDivisorULift' :
    Algebra.GrothendieckAddGroup StageDivisor.{u} →+
      Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp
      stageDivisorULiftEquiv'.toAddMonoidHom)

noncomputable def liftedDivisorMapAligned'
    {L : Type u} [Field L] [Algebra K L]
    (V : DvCoverNormalizedValuationData K L) :
    Additive (ULift.{u+1} Lˣ) →+
      Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
  grothendieckStageDivisorULift'.comp
    (liftedDivisorMap (K := K) (L := L) V)

theorem liftedDivisorMapAligned'_add
    {L : Type u} [Field L] [Algebra K L]
    (V : DvCoverNormalizedValuationData K L)
    (x y : Additive (ULift.{u+1} Lˣ)) :
    liftedDivisorMapAligned' (K := K) (L := L) V (x + y) =
      liftedDivisorMapAligned' (K := K) (L := L) V x +
        liftedDivisorMapAligned' (K := K) (L := L) V y := by
  exact map_add _ x y

noncomputable def example32DivisorAlignedS491
    (V : DvSmallValuationFamily (K := K)) (X : Example32SmallBase K) :
    (example32RationalFunctionsLiftedULift (K := K)).obj X →+
      Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier := by
  let L : DvTriangleFieldCover K := X.objDown.unop
  letI : Field L.obj.obj := L.property.toField
  letI : Algebra K L.obj.obj := inferInstance
  exact liftedDivisorMapAligned' (K := K) (L := L.obj.obj) (V X)

theorem example32DivisorAlignedS491_add
    (V : DvSmallValuationFamily (K := K)) (X : Example32SmallBase K)
    (x y : (example32RationalFunctionsLiftedULift (K := K)).obj X) :
    example32DivisorAlignedS491 K V X (x + y) =
      example32DivisorAlignedS491 K V X x + example32DivisorAlignedS491 K V X y := by
  exact map_add (example32DivisorAlignedS491 K V X) x y

/-- Divisor-only conditional data: fills the S480 Input divisor field;
naturality is deliberately not asserted here. -/
structure Example32DivisorOnlyData where
  valuationFamily : DvSmallValuationFamily (K := K)
  divisor :
    ∀ X : Example32SmallBase K,
      (example32RationalFunctionsLiftedULift (K := K)).obj X →+
        Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier
  divisor_eq : divisor = example32DivisorAlignedS491 K valuationFamily
  divisor_add : ∀ X (x y : (example32RationalFunctionsLiftedULift (K := K)).obj X),
    divisor X (x + y) = divisor X x + divisor X y

noncomputable def example32DivisorOnlyData
    (V : DvSmallValuationFamily (K := K)) :
    Example32DivisorOnlyData K where
  valuationFamily := V
  divisor := example32DivisorAlignedS491 K V
  divisor_eq := rfl
  divisor_add := fun X x y => example32DivisorAlignedS491_add K V X x y


/-- Conditional S480 input with the divisor field filled by the aligned map.
Compatibility and naturality are explicit hypotheses; naturality is not proved here. -/
noncomputable def example32InputDataS491
    (V : DvSmallValuationFamily (K := K))
    (hcompat : DvSmallValuationCompatibility (K := K) V)
    (hnaturality : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y),
      example32DivisorAlignedS491 K V X
          ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
        (example32PhiIsFSM K).gpPullback f
          (example32DivisorAlignedS491 K V Y value)) :
    Example32InputData K where
  valuationFamily := V
  compatibility := hcompat
  divisor := example32DivisorAlignedS491 K V
  divisor_naturality := hnaturality

end LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual

end
