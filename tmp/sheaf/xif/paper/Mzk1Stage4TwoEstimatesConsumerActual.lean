import tmp.sheaf.xif.paper.Mzk1Stage4TwoEstimatesNumericChainActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCTwoEstimatesWrapupActual

/-! # Mzk1Stage4TwoEstimatesConsumerActual (stage4 lane; unique filename)

A605 module: complete consumer record for the two ABC estimates — numeric chain plus
the two-estimates evidence fields.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesNumericChainActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCTwoEstimatesWrapupActual

/-- The complete two-estimates consumer record. -/
structure TwoEstimatesComplete where
  /-- Reduced combined height bound. -/
  combined : (5 / 6 : Real) * Real.log 11 <=
    (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0)
  /-- Numeric Theorem 1.10 instance. -/
  theorem110 : (1 / 6 : Real) * (5 * Real.log 11) <= theorem110RHS
  /-- Numeric Gap 2 witness. -/
  gap2 : ∃ A : Real, (1 : Real) <= (1 + 1 / 10) * 1 + A
  /-- Stage 5 input shape. -/
  stage5 : ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned

/-- Construct the complete consumer record. -/
noncomputable def twoEstimatesComplete : TwoEstimatesComplete where
  combined := twoEstimates_numeric_chain.1
  theorem110 := theorem110_11a1_l13
  gap2 := twoEstimates_numeric_chain.2.2
  stage5 := twoEstimates_stage5_chain.2

/-- Consumer: complete record combined bound. -/
theorem twoEstimatesComplete_combined :
    (5 / 6 : Real) * Real.log 11 <=
      (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  twoEstimatesComplete.combined

/-- Consumer: complete record Stage 5 input. -/
theorem twoEstimatesComplete_stage5 :
    ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned :=
  twoEstimatesComplete.stage5

#check TwoEstimatesComplete
#check twoEstimatesComplete
#check twoEstimatesComplete_combined
#check twoEstimatesComplete_stage5

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesConsumerActual
end
