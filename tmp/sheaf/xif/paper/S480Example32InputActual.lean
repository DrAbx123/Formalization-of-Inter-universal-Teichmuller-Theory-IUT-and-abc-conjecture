import tmp.sheaf.xif.paper.S469RationalFunctionsLiftedActual
import tmp.sheaf.xif.paper.S465LiftedDivisorMapActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import tmp.sheaf.xif.paper.S432SmallModelActual
import Iut.Foundations.SourceModelFrobenioidPresentation

/-! # S480: conditional Example32SmallInput from S469 rational functions

`example32PhiIsFSM` is the constant-N divisorial monoid with IsFSM =
`Example32IsFSM` (units bijectivity), matching S469 rationalFunctions.
`Example32InputData` bundles the explicit valuation family, its compatibility,
and the divisor map/naturality.  From it we build the actual `Input` and the
conditional FrobenioidPresentation.  The divisor map itself is kept explicit
because S465's target universe `StageDivisor.{u}` differs from the u+1
`DivisorialMonoidOn` target; no fake coercion is inserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S480Example32InputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Constant N divisor monoid with the S456/S469 IsFSM predicate. -/
noncomputable def example32PhiIsFSM :
    DivisorialMonoidOn.{u+1} (Example32SmallBase K) (Example32IsFSM (K := K)) where
  obj _ := Iut.SourceFinitePlaceReconstruction.stageDivisorialAddMonoid.{u+1}
  pullback _ := AddMonoidHom.id _
  pullback_id _ := rfl
  pullback_comp _ _ := rfl
  characteristicallyInjective _ := Function.injective_id
  fsmPullbackIsIso _ _ := Function.bijective_id

/-- Conditional data for the Example32SmallInput. -/
structure Example32InputData where
  valuationFamily : DvSmallValuationFamily (K := K)
  compatibility : DvSmallValuationCompatibility (K := K) valuationFamily
  divisor :
    ∀ X : Example32SmallBase K,
      (example32RationalFunctionsLiftedULift (K := K)).obj X →+
        Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y),
      divisor X ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
        (example32PhiIsFSM K).gpPullback f (divisor Y value)

/-- Conditional actual Input. -/
noncomputable def example32InputOfData
    (D : Example32InputData K) :
    Input (example32PhiIsFSM K) where
  rationalFunctions := example32RationalFunctionsLiftedULift (K := K)
  divisor := D.divisor
  divisor_natural := D.divisor_naturality

/-- Conditional actual FrobenioidPresentation. -/
noncomputable def example32FrobenioidPresentationOfData
    (D : Example32InputData K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := example32PhiIsFSM K) (data := example32InputOfData K D)
    baseTotallyEpimorphic

end LeanFormal.IUT.XiFPaper.S480Example32InputActual
end
