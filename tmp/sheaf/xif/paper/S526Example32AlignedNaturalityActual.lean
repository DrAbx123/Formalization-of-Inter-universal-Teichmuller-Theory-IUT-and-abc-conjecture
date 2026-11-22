import tmp.sheaf.xif.paper.S496Example32AlignedDivisorNaturalityActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S526Example32AlignedNaturalityActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S496Example32AlignedDivisorNaturalityActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Evaluation lemma for the aligned divisor on ULifted units. -/
theorem example32AlignedDivisor_ofMul_up
    (V : DvSmallValuationFamily (K := K)) (X : Example32SmallBase K)
    (x : (coverField X)ˣ) :
    example32AlignedDivisor (K := K) V X
        (Additive.ofMul (ULift.up x)) =
      grothendieckStageDivisorULift
        (divisorMap (V X) (Additive.ofMul x)) := by
  rfl

/-- Exact remaining naturality gap after the eval lemma. -/
def example32AlignedDivisorNaturalityGap : Prop :=
  ∀ (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y),
    example32AlignedDivisor (K := K) V X
        ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
      (example32PhiIsFSM K).gpPullback f
        (example32AlignedDivisor (K := K) V Y value)

end LeanFormal.IUT.XiFPaper.S526Example32AlignedNaturalityActual

end
