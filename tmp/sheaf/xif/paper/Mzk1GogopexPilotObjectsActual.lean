import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gogopex Stage1 pilot objects and our StepXI contract

Reference layer over Gogopex `PilotComparison`/`CorollarySchema`: a real
`Stage1Comparison` built from the signed real inequality, and a StepXI
contract whose q/Theta fields are the negated pilot magnitudes. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexPilotObjectsActual

open LeanFormal.IUT
open Iut.Stage1

/-- The Gogopex Stage1 comparison from the signed real inequality. -/
def stage1ComparisonOfSigned (thetaSigned qSigned : Real)
    (hq : 0 < -qSigned) (hle : qSigned ≤ thetaSigned) : Stage1Comparison :=
  stage1Comparison_of_signed_le hq hle

theorem stage1ComparisonOfSigned_comparison (thetaSigned qSigned : Real)
    (hq : 0 < -qSigned) (hle : qSigned ≤ thetaSigned) :
    Corollary312Inequality
      (stage1ComparisonOfSigned thetaSigned qSigned hq hle).theta
      (stage1ComparisonOfSigned thetaSigned qSigned hq hle).q :=
  corollary312_from_stage1_comparison
    (stage1ComparisonOfSigned thetaSigned qSigned hq hle)

theorem stage1ComparisonOfSigned_signed_le (thetaSigned qSigned : Real)
    (hq : 0 < -qSigned) (hle : qSigned ≤ thetaSigned) :
    qSigned ≤ thetaSigned :=
  hle

/-- StepXI contract read from a completed Gogopex Stage1 comparison. -/
def contractOfStage1 (S : Stage1Comparison) : StepXIContract where
  qSigned := -S.q.value
  thetaSigned := -S.theta.value
  targetSigned := -S.theta.value
  q_negative := by linarith [S.q_positive]
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := by
    simpa [Corollary312Inequality] using S.comparison
  target_le_theta := le_rfl

theorem contractOfStage1_conclusion (S : Stage1Comparison) :
    Cor312Conclusion (contractOfStage1 S) :=
  cor312_of_constructed_stepXI (contractOfStage1 S)

end LeanFormal.IUT.XiFPaper.Mzk1GogopexPilotObjectsActual

end
