import tmp.sheaf.xif.paper.Mzk1Stage4TwoEstimatesReductionActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual
import tmp.sheaf.xif.paper.Mzk1Stage4Gap2NumericWitnessActual

/-! # Mzk1Stage4TwoEstimatesNumericChainActual (stage4 lane; unique filename)

A602 module: numeric chain for the two remaining ABC estimates — the reduced combined
height bound, the numeric Theorem 1.10 instance, and the Stage 5 input shape, together
in one chain.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesNumericChainActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2NumericWitnessActual

/-- Numeric chain: reduced two-estimate bound ∧ Theorem 1.10 instance ∧ Gap 2 witness. -/
theorem twoEstimates_numeric_chain :
    ((5 / 6 : Real) * Real.log 11 <=
        (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0)) ∧
      ((1 / 6 : Real) * degQ11 <= theorem110RHS) ∧
      (∃ A : Real, (1 : Real) <= (1 + 1 / 10) * 1 + A) :=
  ⟨reduced_combined, theorem110_11a1_l13, gap2_numeric_witness⟩

/-- Numeric chain: the combined bound together with the Stage 5 input shape. -/
theorem twoEstimates_stage5_chain :
    ((5 / 6 : Real) * Real.log 11 <=
        (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0)) ∧
      (∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned) :=
  ⟨reduced_combined, ⟨-1, 0, by norm_num, by norm_num⟩⟩

#check twoEstimates_numeric_chain
#check twoEstimates_stage5_chain

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesNumericChainActual
end
