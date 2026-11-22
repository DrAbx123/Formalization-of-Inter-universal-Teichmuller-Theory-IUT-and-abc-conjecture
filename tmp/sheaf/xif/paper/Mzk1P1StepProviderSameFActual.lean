import tmp.sheaf.xif.paper.Mzk1P1StepProviderStrictConsumerActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridgeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepProviderSameFActual — finite stable-branch identity from the P1 one (real)

Real Lean (no sorry/axiom): if the P1 step target keeps the maximal degree
(maxDegP stepSetP1 = maxDegP S, with maxDegP S >= 2), then the finite step target keeps the
finite-part maximal degree.  This discharges the last hypothesis of the f4b consumer.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderSameFActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartMeasureActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridgeActual

universe u

theorem maxDeg_stepSet_eq_of_same
    (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (h2 : 2 <= maxDegP S)
    (hsame : maxDegP (stepSetP1 S alpha0) = maxDegP S) :
    maxDeg (stepSet (finitePart S) alpha0) = maxDeg (finitePart S) := by
  have hM : maxDegP S = maxDeg (finitePart S) := maxDegP_eq_maxDeg_finitePart S h2
  have h2M : 2 <= maxDeg (finitePart S) := by rw [← hM]; exact h2
  have hdec := stepSetP1_eq_finite S alpha0
  by_cases hinf : P1Point.infty ∈ S
  · have hset : stepSetP1 S alpha0 =
        insert P1Point.infty ((stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x)) := by
      rw [hdec, if_pos hinf]
      ext q
      by_cases hq : q = P1Point.infty
      · subst hq
        simp
      · simp [hq]
    rw [hset, maxDegP_insert_infty_image] at hsame
    have hmax : max 1 (maxDeg (stepSet (finitePart S) alpha0)) = maxDeg (finitePart S) := by
      rw [hsame, hM]
    have hxle : maxDeg (stepSet (finitePart S) alpha0) <= maxDeg (finitePart S) :=
      le_trans (le_max_right _ _) (le_of_eq hmax)
    have hyle : maxDeg (finitePart S) <= maxDeg (stepSet (finitePart S) alpha0) := by
      rcases le_or_lt (maxDeg (finitePart S)) (maxDeg (stepSet (finitePart S) alpha0)) with hle | hlt
      · exact hle
      · -- max = maxDeg F >= 2 while the other is smaller: forced max = 1, contradiction
        have h1 : max 1 (maxDeg (stepSet (finitePart S) alpha0)) = 1 := by
          rw [max_eq_left]
          omega
        rw [h1] at hmax
        omega
    exact le_antisymm hxle hyle
  · have hset : stepSetP1 S alpha0 =
        (stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x) := by
      rw [hdec, if_neg hinf]
      exact Finset.union_empty _
    rw [hset, maxDegP_image_ofFinite] at hsame
    rw [hsame, hM]

#check maxDeg_stepSet_eq_of_same

end LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderSameFActual
end
