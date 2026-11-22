/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperStepVBoxActual
import tmp.sheaf.xif.paper.Mzk1TargetReductionActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import tmp.sheaf.xif.paper.Mzk1ThetaDataLegalityActual
import Mathlib.Tactic

/-! # GAP-P3-DICT first segment (DICT-A): box slack + T(l) denominator dictionary

Green inputs only (paper StepV box algebra, T(l) definition, L6 definition).
Two named gaps remain: DICT-B (paper objects ↔ arithmetic quantities) and
DICT-C (box upper bound ⟷ L6 lower bound).  See `coord/P3-TARGET-EQUIV.md` §6.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- The paper StepV box slack: `RHS - LHS` of the paper Step-V inequality. -/
def boxSlack (l D Q S Tstar : ℝ) : ℝ := paperRHS l D Q S Tstar - paperLHS l D Q S Tstar

/-- Exact formula for the box slack (pure algebra; `Q` cancels). -/
theorem boxSlack_eq (l D Q S Tstar : ℝ) (hl : l ≠ 0) :
    boxSlack l D Q S Tstar =
      (1 / l) * D + (1 / l) * S + ((2 * l - 10) / 3) * Tstar := by
  unfold boxSlack paperLHS paperRHS
  field_simp [hl]
  ring

/-- Box inequality ⟺ nonnegative slack. -/
theorem paperStepV_iff_slack_nonneg (l D Q S Tstar : ℝ) :
    paperLHS l D Q S Tstar ≤ paperRHS l D Q S Tstar ↔ 0 ≤ boxSlack l D Q S Tstar := by
  unfold boxSlack
  constructor <;> intro h <;> linarith

/-- `T(l)` is positive for `l ≥ 5` (denominator positive). -/
theorem T_pos_of_five_le {l : ℝ} (hl : 5 ≤ l) : 0 < T l := by
  unfold T
  have h4 : (0 : ℝ) < l + 4 := by linarith
  have h3 : (0 : ℝ) < l - 3 := by linarith
  positivity

/-- **T(l) denominator dictionary (green arithmetic)**: for `l > 3`,
`e·log p ≤ T(l)·D` is equivalent to the polynomial form
`e·log p · ((l+4)(l-3)) ≤ 6·l·(l+5)·D` (multiply by the positive denominator). -/
theorem l6_iff_scaled (C : PrimeConductorCurve) (l D_exact : ℝ) (hl : 3 < l) :
    L6ReducedInequality C l D_exact ↔
      (C.e : ℝ) * Real.log (C.p : ℝ) * ((l + 4) * (l - 3)) ≤
        6 * l * (l + 5) * D_exact := by
  unfold L6ReducedInequality T
  have h4 : (0 : ℝ) < l + 4 := by linarith
  have h3 : (0 : ℝ) < l - 3 := by linarith
  have hden : (0 : ℝ) < (l + 4) * (l - 3) := mul_pos h4 h3
  constructor
  · intro h
    rw [div_mul_eq_mul_div] at h
    exact (le_div_iff₀ hden).mp h
  · intro h
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).mpr h

/-- **Conditional target ⇔ box inequality** (DICT-B explicit input):
if `M = c1 · boxSlack` with `c1 > 0`, then `M ≥ 0` is equivalent to the paper
Step-V box inequality. -/
theorem targetM_nonneg_iff_paperBox
    {V gap sF A l D Q S Tstar c1 : ℝ} (hc1 : 0 < c1)
    (hDICTB : MExpr V gap sF A = c1 * boxSlack l D Q S Tstar) :
    0 ≤ MExpr V gap sF A ↔ paperLHS l D Q S Tstar ≤ paperRHS l D Q S Tstar := by
  rw [hDICTB, paperStepV_iff_slack_nonneg]
  constructor
  · intro h; exact (mul_nonneg_iff_of_pos_left hc1).mp h
  · intro h; exact (mul_nonneg_iff_of_pos_left hc1).mpr h

/-- **Target ⇔ L6 via two named dictionaries**:
`M = c1·boxSlack` (DICT-B, hypothesis) and `0 ≤ boxSlack ↔ L6ReducedInequality`
(DICT-C, hypothesis).  Both are explicit inputs; no object is constructed here. -/
theorem targetM_nonneg_iff_L6_of_dicts
    {V gap sF A l D Q S Tstar c1 : ℝ} (hc1 : 0 < c1)
    (hDICTB : MExpr V gap sF A = c1 * boxSlack l D Q S Tstar)
    (C : PrimeConductorCurve) (D_exact : ℝ)
    (hDICTC : 0 ≤ boxSlack l D Q S Tstar ↔ L6ReducedInequality C l D_exact) :
    0 ≤ MExpr V gap sF A ↔ L6ReducedInequality C l D_exact := by
  rw [targetM_nonneg_iff_paperBox hc1 hDICTB, paperStepV_iff_slack_nonneg, hDICTC]

/-- Status rows. -/
def p3DictionaryRows : List (String × String × String) :=
  [ ("boxSlack", "paperRHS - paperLHS", "DEF"),
    ("boxSlack_eq", "slack = (1/l)D + (1/l)S + ((2l-10)/3)T", "PROVED (algebra)"),
    ("paperStepV_iff_slack_nonneg", "paper LHS<=RHS <=> 0<=slack", "PROVED"),
    ("T_pos_of_five_le", "0 < T(l) for l>=5", "PROVED"),
    ("l6_iff_scaled", "L6 <=> e logp ((l+4)(l-3)) <= 6l(l+5)D", "PROVED (arithmetic)"),
    ("targetM_nonneg_iff_paperBox", "M>=0 <=> box inequality, given M=c1*slack", "PROVED (conditional DICT-B)"),
    ("targetM_nonneg_iff_L6_of_dicts", "M>=0 <=> L6, given DICT-B + DICT-C", "PROVED (conditional)"),
    ("DICT-B", "paper (D,Q,S,T) <-> arithmetic quantities", "GAP"),
    ("DICT-C", "box upper bound <-> L6 lower bound direction", "GAP (one-way only in tree)") ]

theorem p3DictionaryRows_length : p3DictionaryRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual

end
