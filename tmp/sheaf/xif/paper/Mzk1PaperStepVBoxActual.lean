/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A819 hull: paper Step-V box (original IUT IV Thm 1.10 Step(v))

Paper inequality (D = log d^K, Q = log q, S = log s^Q, T = l*_mod log s≤):

  `((l+5)/4)D − ((l+1)/24)Q + S + (l+5)T
    <= ((l+1)/4)·((1+4/l)D − Q/6 + (4/l)S + (20/3)T)`.

Elementarily the `Q` coefficients cancel, and the difference is
`(1/l)D + (1/l)S + ((2l−10)/3)T >= 0` for `l >= 5` and nonnegative D,S,T.
Thus the paper inequality closes without any absolute-constant claim.
The Section-1 bookkeeping identifying `(l+5)T` with the procession R4
(`StepVProcessionAverage.exceptionalSum_le_r4`) and `S` with Section-1 data
is listed as the remaining dictionary. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual

def paperLHS (l D Q S T : ℝ) : ℝ :=
  ((l + 5) / 4) * D - ((l + 1) / 24) * Q + S + (l + 5) * T

def paperRHS (l D Q S T : ℝ) : ℝ :=
  ((l + 1) / 4) * ((1 + 4 / l) * D - Q / 6 + (4 / l) * S + (20 / 3) * T)

theorem paperRHS_expand (l D Q S T : ℝ) (hl : l ≠ 0) :
    paperRHS l D Q S T =
      ((l + 1) / 4) * D + ((l + 1) / l) * D - ((l + 1) / 24) * Q +
        ((l + 1) / l) * S + ((l + 1) / 4) * ((20 / 3) * T) := by
  unfold paperRHS
  field_simp [hl]
  ring

/-- **Paper Step-V inequality** (original form): for `l >= 5` and
`D,S,T >= 0` the paper LHS is at most the paper RHS.  `Q` cancels exactly. -/
theorem paperStepV_inequality (l D Q S T : ℝ) (hl : 5 ≤ l)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    paperLHS l D Q S T ≤ paperRHS l D Q S T := by
  have hl0 : 0 < l := by linarith
  have hlne : l ≠ 0 := ne_of_gt hl0
  have hdiff : paperRHS l D Q S T - paperLHS l D Q S T =
      (1 / l) * D + (1 / l) * S + ((2 * l - 10) / 3) * T := by
    unfold paperLHS paperRHS
    field_simp [hlne]
    ring
  have h1 : 0 ≤ (1 / l) * D := mul_nonneg (one_div_nonneg.mpr hl0.le) hD
  have h2 : 0 ≤ (1 / l) * S := mul_nonneg (one_div_nonneg.mpr hl0.le) hS
  have hcoef : 0 ≤ (2 * l - 10) / 3 := by nlinarith
  have h3 : 0 ≤ ((2 * l - 10) / 3) * T := mul_nonneg hcoef hT
  linarith

/-- Paper box form: the paper RHS is the `(l+1)/4`-scaled box; no absolute
constant or `6` is claimed. -/
def paperBoxRHS (l D Q S T : ℝ) : ℝ := paperRHS l D Q S T

theorem paperBoxRHS_eq (l D Q S T : ℝ) :
    paperBoxRHS l D Q S T = paperRHS l D Q S T := rfl

def paperStepVRows : List (String × String × String) :=
  [ ("paper LHS", "((l+5)/4)D - ((l+1)/24)Q + S + (l+5)T", "DEF (paperLHS)"),
    ("paper RHS", "((l+1)/4)((1+4/l)D - Q/6 + (4/l)S + (20/3)T)", "DEF (paperRHS)"),
    ("paper inequality", "LHS <= RHS for l>=5, D,S,T>=0 (Q cancels)", "PROVED (paperStepV_inequality)"),
    ("difference", "RHS-LHS = (1/l)D + (1/l)S + ((2l-10)/3)T >= 0", "STRUCTURE"),
    ("no strong constant", "no absolute 6 claim; finite l coefficient is 6(1+eps(l))", "INTEGRITY"),
    ("Section-1 dictionary", "identify (l+5)T with procession R4 green exceptionalSum_le_r4, S with log s^Q", "GAP" ),
    ("green inputs", "StepVProcessionAverage.exceptionalSum_le_r4; IntegralLogShellSharpBounds A/B", "GREEN cited") ]

theorem paperStepVRows_length : paperStepVRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual.paperStepV_inequality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual.paperRHS_expand

end LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual

end