import tmp.sheaf.xif.paper.Mzk1P1StepProviderStrictConsumerActual
import tmp.sheaf.xif.paper.Mzk1P1StepProviderSameFActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepProviderF4bActual — f4b: P1 strict numMax count (assembled, real)

Real Lean (no sorry/axiom): the paper's f4b statement for the P1 step target, assembled from
the PROVED finite strict-count lemma numMax_stepSet_lt via:
  Mzk1P1FinitePartActual (finite part),
  Mzk1P1FinitePartMeasureActual (P1 measure = finite-part measure),
  Mzk1P1StepProviderDecompositionActual (step-target decomposition),
  Mzk1P1StepProviderStrictActual (finite -> P1 transfer),
  Mzk1P1StepProviderStrictConsumerActual (assumption discharge),
  Mzk1P1StepProviderSameFActual (finite stable-branch identity from the P1 one).
Hypotheses are exactly the paper's stable-branch conditions.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderF4bActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderStrictConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderSameFActual

universe u

/-- **f4b (assembled):** on the stable-max-degree branch, the P1 maximal count of the paper's
step target strictly drops. -/
theorem numMaxP_stepSetP1_lt (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (h2 : 2 <= maxDegP S)
    (halpha0S : P1Point.ofFinite alpha0 ∈ S)
    (hdeg : degQ alpha0 = maxDegP S)
    (hsame : maxDegP (stepSetP1 S alpha0) = maxDegP S) :
    numMaxP (stepSetP1 S alpha0) < numMaxP S :=
  numMaxP_stepSetP1_lt_consumer S alpha0 h2 halpha0S hdeg
    (maxDeg_stepSet_eq_of_same S alpha0 h2 hsame)

/-- Consumer alias for the assembled f4b. -/
theorem f4b_numMaxP_stepSetP1_lt := numMaxP_stepSetP1_lt

#check numMaxP_stepSetP1_lt

end LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderF4bActual
end
