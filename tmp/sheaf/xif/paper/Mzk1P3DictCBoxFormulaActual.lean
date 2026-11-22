import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import Mathlib.Tactic

/-! # GREEN: paper box slack formula and nonnegativity condition -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCBoxFormulaActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual

/-- Exact slack formula with the Q cancelled. -/
theorem slack_formula (l D Q S Tstar : Real) (hl : l ≠ 0) :
    boxSlack l D Q S Tstar =
      (1 / l) * D + (1 / l) * S + ((2 * l - 10) / 3) * Tstar :=
  boxSlack_eq l D Q S Tstar hl

/-- Explicit sufficient condition for nonnegative slack. -/
theorem slack_nonneg_of_nonneg
    (l D Q S Tstar : Real) (hl : 5 <= l)
    (hD : 0 <= D) (hS : 0 <= S) (hT : 0 <= Tstar) :
    0 <= boxSlack l D Q S Tstar := by
  have hlpos : 0 < l := by linarith
  rw [slack_formula l D Q S Tstar (ne_of_gt hlpos)]
  have h1 : 0 <= (1 / l) * D :=
    mul_nonneg (one_div_nonneg.mpr hlpos.le) hD
  have h2 : 0 <= (1 / l) * S :=
    mul_nonneg (one_div_nonneg.mpr hlpos.le) hS
  have hcoef : 0 <= (2 * l - 10) / 3 := by nlinarith
  have h3 : 0 <= ((2 * l - 10) / 3) * Tstar := mul_nonneg hcoef hT
  linarith

#check slack_formula
#check slack_nonneg_of_nonneg
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCBoxFormulaActual
end
