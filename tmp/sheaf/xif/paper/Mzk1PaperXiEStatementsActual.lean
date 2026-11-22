import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Paper Cor 3.12 statement shape and non-vacuity check

IUT III 10324-10353: both pilot log-volumes are real-valued (finiteness),
qSigned = -|log q| < 0, and the conclusion is qSigned <= thetaSigned, i.e.
`-|log q| <= -|log Theta|`.  This file records the exact statement shape and
checks that strict (non-reflexive) data is possible. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperXiEStatementsActual

/-- Exact paper-shaped Cor 3.12 statement at the level of signed readings. -/
structure PaperCor312Statement where
  /-- `-|log(q)|` -/
  qSigned : Real
  /-- `-|log(Theta)|` -/
  thetaSigned : Real
  q_negative : qSigned < 0
  cor312_inequality : qSigned <= thetaSigned

theorem paper_shape_iff (qSigned thetaSigned : Real) (hq : qSigned < 0) :
    (qSigned <= thetaSigned) ↔
      ∃ _ : qSigned < 0, qSigned <= thetaSigned := by
  constructor
  · intro h
    exact ⟨hq, h⟩
  · rintro ⟨_, h⟩; exact h

/-- Non-vacuity: a strict pair satisfying the paper shape exists. -/
theorem strict_paper_shape_witness :
    ∃ P : PaperCor312Statement, P.qSigned < P.thetaSigned := by
  refine ⟨⟨-2, -1, by norm_num, by norm_num⟩, by norm_num⟩

/-- The assembled shape is not reflexive: strict data has q < theta, not equality. -/
theorem paper_shape_not_defeq (P : PaperCor312Statement)
    (h : P.qSigned < P.thetaSigned) :
    P.qSigned ≠ P.thetaSigned := by
  exact ne_of_lt h

end LeanFormal.IUT.XiFPaper.Mzk1PaperXiEStatementsActual

end
