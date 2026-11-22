import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesGapReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesIntermediateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates normalization instance

Explicit half-epsilon instance of the two-gap δ-selection and the resulting ABC
reduction. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesNormalizationActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesIntermediateActual

theorem stepxi_twoEstimates_half (I : StepXIABCTwoGaps) :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + (1 : Real) / 2 ∧
      ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        I.logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          I.hullVolume + D :=
  twoGaps_delta_selection I (by norm_num)

theorem stepxi_twoEstimates_half_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesNormalizationActual

end
