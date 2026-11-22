import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi weight/naive-coefficient counterexample

The naive theta coefficient `l(l+1)/12` fails the paper comparison at `l=13`:
`13*14/12 = 91/6 > 1`.  This is the numeric obstruction recorded by A-series. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIWeightCounterexampleActual

/-- Paper `|log q| = m log p /(2l)` model. -/
def paperAbsLogQ (l : Nat) (logq : Real) : Real := logq / (2 * (l : Real))

/-- Naive procession theta coefficient `l(l+1)/12`. -/
def naiveThetaCoefficient (l : Nat) : Real := (l : Real) * ((l : Real) + 1) / 12

theorem naiveThetaCoefficient_thirteen :
    naiveThetaCoefficient 13 = 91 / 6 := by
  unfold naiveThetaCoefficient
  norm_num

theorem l13_naive_fails : ¬ (naiveThetaCoefficient 13 ≤ 1) := by
  rw [naiveThetaCoefficient_thirteen]
  norm_num

theorem naiveComparison_iff (l : Nat) (hl : 0 < l) {logq : Real} (hlogq : 0 < logq) :
    -(paperAbsLogQ l logq) ≤ -(naiveThetaCoefficient l * paperAbsLogQ l logq) ↔
      naiveThetaCoefficient l ≤ 1 := by
  have hA : 0 < paperAbsLogQ l logq := by
    unfold paperAbsLogQ
    positivity
  constructor <;> intro h <;> nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXIWeightCounterexampleActual

end
