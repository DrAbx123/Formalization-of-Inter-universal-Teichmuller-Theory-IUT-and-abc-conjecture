import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesIntermediateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates gap reduction

Intermediate reduction: the two explicit estimates directly give the ABC-form
additive height bound at every epsilon. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesGapReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesIntermediateActual

theorem stepxi_twoEstimates_epsilon (I : StepXIABCTwoGaps) {ε : Real} (hε : 0 < ε) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxi_twoGaps_abcForm I ε hε

theorem stepxi_twoEstimates_BC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesGapReductionActual

end
