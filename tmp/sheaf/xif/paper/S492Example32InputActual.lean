import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S469RationalFunctionsLiftedActual
import tmp.sheaf.xif.paper.S480Example32InputActual
import Iut.Foundations.SourceModelFrobenioidPresentation

/-! # S492: fill S480 divisor with S481 actual aligned divisor

New conditional Input data: only the valuation family and the divisor
naturality are assumed.  `rationalFunctions` is S469 actual; `divisor` is the
actual S481 aligned map; the resulting `Input` and FrobenioidPresentation are
constructed directly.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S492Example32InputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Conditional data with actual S481 divisor. -/
structure Example32InputDataActual where
  valuationFamily : DvSmallValuationFamily (K := K)
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y),
      example32AlignedDivisor (K := K) valuationFamily X
          ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
        (example32PhiIsFSM K).gpPullback f
          (example32AlignedDivisor (K := K) valuationFamily Y value)

/-- Conditional actual Input with S469 rationalFunctions and S481 divisor. -/
noncomputable def example32InputActual
    (D : Example32InputDataActual K) :
    Input (example32PhiIsFSM K) where
  rationalFunctions := example32RationalFunctionsLiftedULift (K := K)
  divisor X := example32AlignedDivisor (K := K) D.valuationFamily X
  divisor_natural := D.divisor_naturality

/-- The rationalFunctions field is the S469 actual object. -/
theorem example32InputActual_rationalFunctions
    (D : Example32InputDataActual K) :
    (example32InputActual K D).rationalFunctions =
      example32RationalFunctionsLiftedULift (K := K) := rfl

/-- The divisor field is the S481 actual aligned divisor. -/
theorem example32InputActual_divisor
    (D : Example32InputDataActual K) :
    (example32InputActual K D).divisor =
      fun X => example32AlignedDivisor (K := K) D.valuationFamily X := rfl

/-- Conditional actual FrobenioidPresentation. -/
noncomputable def example32FrobenioidPresentationActual
    (D : Example32InputDataActual K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := example32PhiIsFSM K) (data := example32InputActual K D)
    baseTotallyEpimorphic

end LeanFormal.IUT.XiFPaper.S492Example32InputActual
end
