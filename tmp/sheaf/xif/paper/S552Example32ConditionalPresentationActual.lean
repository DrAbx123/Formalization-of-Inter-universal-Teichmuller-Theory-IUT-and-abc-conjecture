import tmp.sheaf.xif.paper.S544Example32AlignedTypeLemmaActual
import tmp.sheaf.xif.paper.S492Example32InputActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S552Example32ConditionalPresentationActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S492Example32InputActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S544Example32AlignedTypeLemmaActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Exact conditions still required by S492's presentation constructor. -/
structure Example32PresentationConditions where
  baseConnected : CategoryTheory.IsConnected (Example32SmallBase K)
  baseTotallyEpimorphic :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f

/-- Conditional actual Input with S544 naturality. -/
noncomputable def example32InputOfValuation
    (V : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (hV : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationCompatibility (K := K) V) :
    Input (example32PhiIsFSM K) :=
  @example32InputActual K inferInstance
    (example32InputDataActualOfValuation (K := K) V hV)

/-- Conditional actual FrobenioidPresentation from explicit V/hV and the two
category conditions. -/
noncomputable def example32FrobenioidPresentationConditional
    (V : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (hV : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationCompatibility (K := K) V)
    (C : Example32PresentationConditions K) :
    Iut.FrobenioidPresentation := by
  letI : IsConnected (Example32SmallBase K) := C.baseConnected
  exact @example32FrobenioidPresentationActual K inferInstance
    (example32InputDataActualOfValuation (K := K) V hV)
    C.baseConnected C.baseTotallyEpimorphic

/-- The Input rationalFunctions field is S469 actual. -/
theorem example32InputOfValuation_rationalFunctions
    (V : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (hV : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationCompatibility (K := K) V) :
    (example32InputOfValuation (K := K) V hV).rationalFunctions =
      example32RationalFunctionsLiftedULift (K := K) := by
  change (@example32InputActual K inferInstance
    (example32InputDataActualOfValuation (K := K) V hV)).rationalFunctions =
      example32RationalFunctionsLiftedULift (K := K)
  exact example32InputActual_rationalFunctions _ _

/-- The Input divisor field is S481 actual aligned divisor. -/
theorem example32InputOfValuation_divisor
    (V : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (hV : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationCompatibility (K := K) V) :
    (example32InputOfValuation (K := K) V hV).divisor =
      fun X => example32AlignedDivisor (K := K) V X := by
  change (@example32InputActual K inferInstance
    (example32InputDataActualOfValuation (K := K) V hV)).divisor =
      fun X => example32AlignedDivisor (K := K) V X
  exact example32InputActual_divisor _ _

end LeanFormal.IUT.XiFPaper.S552Example32ConditionalPresentationActual

end
