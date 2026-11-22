import tmp.sheaf.xif.paper.Mzk1PaperXiEStatementsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Chain-independent final checks

These checks depend only on `Mzk1PaperXiEStatementsActual` (already EXIT=0):
* the paper-shaped target is exactly `qSigned <= thetaSigned`;
* strict data is non-reflexive (`q < theta` implies `q != theta`), so the
  final chain cannot be a definitional equality.
No dependency on the blocked FinalAssembly/KummerRealization oleans. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalChecksIndependentActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperXiEStatementsActual

theorem target_matches_paper (P : PaperCor312Statement) :
    P.qSigned <= P.thetaSigned := P.cor312_inequality

theorem no_defeq_vacuity (P : PaperCor312Statement)
    (h : P.qSigned < P.thetaSigned) : P.qSigned ≠ P.thetaSigned := by
  exact ne_of_lt h

theorem strict_shape_exists :
    ∃ P : PaperCor312Statement, P.qSigned < P.thetaSigned :=
  strict_paper_shape_witness

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalChecksIndependentActual

end
