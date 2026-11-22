import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesGapReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates half-epsilon consequence

Explicit half-epsilon height bound and ABC consequence. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesConsequenceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesGapReductionActual

theorem stepxi_twoEstimates_half_height (I : StepXIABCTwoGaps) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + (1 : Real) / 2) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxi_twoEstimates_epsilon I (by norm_num)

theorem stepxi_twoEstimates_half_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoEstimates_BC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesConsequenceActual

end
