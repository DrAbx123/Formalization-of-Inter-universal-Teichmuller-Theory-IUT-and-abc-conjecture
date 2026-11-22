import tmp.sheaf.xif.paper.Mzk1PaperXiEStatementsActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Numeric paper-shape consumer at l=13

Paper signed q magnitude at one bad p=11, m=5, l=13 is `5 log 11/(2*13)`.
The following witness uses a Theta signed value `-log 11/10` (strictly above q,
still negative); it checks the exact shape `q < theta < 0` required by Cor 3.12
after choosing a strict paper reading.  No structural claim is made; this is an
arithmetic consumer of `PaperCor312Statement`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperXiENumericConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperXiEStatementsActual

theorem numeric_paper_shape_l13 :
    ∃ P : PaperCor312Statement,
      P.qSigned = -((5 : Real) * Real.log (11 : Real) / (2 * 13)) ∧
      P.thetaSigned = -((1 : Real) * Real.log (11 : Real) / 10) ∧
      P.qSigned < P.thetaSigned := by
  have hlog : 0 < Real.log (11 : Real) := Real.log_pos (by norm_num)
  have hqneg : -((5 : Real) * Real.log 11 / 26) < 0 := by nlinarith [hlog]
  have hle : -((5 : Real) * Real.log 11 / 26) ≤ -((1 : Real) * Real.log 11 / 10) := by
    nlinarith [hlog]
  let P : PaperCor312Statement := {
    qSigned := -((5 : Real) * Real.log 11 / 26)
    thetaSigned := -((1 : Real) * Real.log 11 / 10)
    q_negative := hqneg
    cor312_inequality := hle }
  refine ⟨P, ?_, ?_, ?_⟩
  · simp [P]
  · simp [P]
  · simp [P]
    nlinarith [hlog]

end LeanFormal.IUT.XiFPaper.Mzk1PaperXiENumericConsumerActual

end
