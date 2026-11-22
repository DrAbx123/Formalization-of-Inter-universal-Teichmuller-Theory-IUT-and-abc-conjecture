import tmp.sheaf.xif.paper.S526Example32AlignedNaturalityActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S536Example32AlignedNaturalityFinalActualAdapted

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
open LeanFormal.IUT.XiFPaper.S526Example32AlignedNaturalityActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

theorem example32AlignedDivisor_naturality
    (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y) :
    example32AlignedDivisor (K := K) V X
        ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
      (example32PhiIsFSM K).gpPullback f
        (example32AlignedDivisor (K := K) V Y value) := by
  let u : (coverField Y)ˣ := value.toMul.down
  have hval : value = Additive.ofMul (ULift.up u) := by
    apply Additive.ext
    apply ULift.ext
    rfl
  rw [hval]
  have h := congrArg grothendieckStageDivisorULift
    (divisorMap_naturality (K := K) V hV f u)
  simpa [phi_gpPullback_id, example32AlignedDivisor_ofMul_up,
    liftedPullback_ofMul_up] using h

end LeanFormal.IUT.XiFPaper.S536Example32AlignedNaturalityFinalActualAdapted

end
