import tmp.sheaf.xif.paper.S526Example32AlignedNaturalityActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S544Example32AlignedTypeLemmaActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S492Example32InputActual
open LeanFormal.IUT.XiFPaper.S496Example32AlignedDivisorNaturalityActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

theorem example32AlignedDivisor_as_S469_obj
    (V : DvSmallValuationFamily (K := K)) (X : Example32SmallBase K)
    (z : (example32RationalFunctionsLiftedULift (K := K)).obj X) :
    example32AlignedDivisor (K := K) V X z =
      grothendieckStageDivisorULift
        (divisorMap (V X) (Additive.ofMul z.toMul.down)) := by
  rfl

theorem example32AlignedDivisor_naturality
    (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y) :
    example32AlignedDivisor (K := K) V X
        ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
      (example32PhiIsFSM K).gpPullback f
        (example32AlignedDivisor (K := K) V Y value) := by
  let z := (example32RationalFunctionsLiftedULift (K := K)).pullback f value
  change example32AlignedDivisor (K := K) V X z =
    (example32PhiIsFSM K).gpPullback f
      (example32AlignedDivisor (K := K) V Y value)
  rw [example32AlignedDivisor_as_S469_obj (K := K) V X z]
  rw [phi_gpPullback_id]
  rw [example32AlignedDivisor_as_S469_obj (K := K) V Y value]
  change grothendieckStageDivisorULift
      (divisorMap (V X) (Additive.ofMul z.toMul.down)) =
    grothendieckStageDivisorULift
      (divisorMap (V Y) (Additive.ofMul value.toMul.down))
  have hz : z.toMul.down = unitInclusionPullback f value.toMul.down := rfl
  rw [hz]
  exact congrArg grothendieckStageDivisorULift
    (divisorMap_naturality (K := K) V hV f value.toMul.down)

/-- Conditional S492 input data with the fully proved divisor naturality. -/
noncomputable def example32InputDataActualOfValuation
    (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V) :
    Example32InputDataActual K where
  valuationFamily := V
  divisor_naturality := example32AlignedDivisor_naturality (K := K) V hV

/-- S526 naturality gap is inhabited. -/
theorem example32AlignedDivisorNaturalityGap_holds :
    example32AlignedDivisorNaturalityGap (K := K) := by
  intro V hV X Y f value
  exact example32AlignedDivisor_naturality (K := K) V hV f value

end LeanFormal.IUT.XiFPaper.S544Example32AlignedTypeLemmaActual

end
