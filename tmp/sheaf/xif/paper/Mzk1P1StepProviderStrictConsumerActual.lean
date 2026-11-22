import tmp.sheaf.xif.paper.Mzk1P1StepProviderStrictActual
import tmp.sheaf.xif.paper.Mzk1P1StepProviderDecompositionActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepProviderStrictConsumerActual — f4b: P1 strict count, assumptions discharged

Real Lean (no sorry/axiom): consumer of the decomposition + transfer, giving the P1 strict
numMax drop on the stable-max-degree branch, with the set-decomposition assumptions removed.
The remaining two hypotheses are the paper's shelf conditions (alpha0 maximal finite point,
and the finite stable-branch max-degree identity).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartMeasureActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderDecompositionActual

local instance instDecEqQbar : DecidableEq Qbar := Classical.decEq Qbar
local instance instDecEqP1 : DecidableEq (P1Point Qbar) := Classical.decEq (P1Point Qbar)

universe u

/-- f4b (consumer form): P1 strict numMax drop with the decomposition discharged. -/
theorem numMaxP_stepSetP1_lt_consumer
    (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (h2 : 2 <= maxDegP S)
    (halpha0S : P1Point.ofFinite alpha0 ∈ S)
    (hdeg : degQ alpha0 = maxDegP S)
    (hsameF : maxDeg (stepSet (finitePart S) alpha0) = maxDeg (finitePart S)) :
    numMaxP (stepSetP1 S alpha0) < numMaxP S := by
  have hdec := stepSetP1_eq_finite S alpha0
  have hstep : stepSetP1 S alpha0 =
        (stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x) ∨
      stepSetP1 S alpha0 =
        insert P1Point.infty ((stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x)) := by
    by_cases hinf : P1Point.infty ∈ S
    · right
      rw [hdec, if_pos hinf, Finset.insert_eq, Finset.union_comm]
    · left
      rw [hdec, if_neg hinf]
      exact Finset.union_empty _
  exact numMaxP_stepSetP1_lt_of_finite S alpha0 h2 halpha0S hdeg hstep
    (mem_finitePart_iff.mpr halpha0S)
    (by rw [hdeg, maxDegP_eq_maxDeg_finitePart S h2])
    (by rw [← maxDegP_eq_maxDeg_finitePart S h2]; exact h2)
    hsameF

#check numMaxP_stepSetP1_lt_consumer

end LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictConsumerActual
end
