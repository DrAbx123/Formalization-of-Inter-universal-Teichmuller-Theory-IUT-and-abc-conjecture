import tmp.sheaf.xif.paper.Mzk1PaperXiEStatementsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Paper statement consumer checks

Consumer of `PaperCor312Statement`: the exact Cor 3.12 inequality shape and the
strict non-reflexivity witness.  No dependency on the blocked Kummer transport. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperXiEConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperXiEStatementsActual

theorem paper_consumer_signed (P : PaperCor312Statement) :
    P.qSigned <= P.thetaSigned := P.cor312_inequality

theorem paper_consumer_strict_witness :
    ∃ P : PaperCor312Statement, P.qSigned < P.thetaSigned :=
  strict_paper_shape_witness

theorem paper_consumer_not_definitional (P : PaperCor312Statement)
    (h : P.qSigned < P.thetaSigned) : P.qSigned ≠ P.thetaSigned :=
  paper_shape_not_defeq P h

end LeanFormal.IUT.XiFPaper.Mzk1PaperXiEConsumerActual

end
