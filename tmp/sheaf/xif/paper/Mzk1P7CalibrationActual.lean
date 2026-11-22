/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7 calibration: `sFactor` vs `2ℓ·c_V` (A763)

P7 of `coord/STEP-XI-SPEC.md` says the procession average gives the coefficient
`(sFactor−1)/(2ℓ)` in ABC-normalized form, and A763 calibrates `c_V = 1/4`
(Szpiro constant 6).  The exact relations are:

* lana coefficient: `sFactor(nC) - 1 = 2ℓ · c_lana`,
  `c_lana := (sFactor(nC)-1)/(2ℓ)` (definitional);
* A763 `c_V = 1/4` gives the closed form
  `sFactor(nC) = ℓ(ℓ+1)/12 = ((ℓ+1)/6)·(2ℓ·c_V)` for `nC = (ℓ−1)/2`;
* `(sFactor−1) = 2ℓ·c_V` is FALSE in general: for ℓ=13,
  `sFactor(6)-1 = 85/6` while `2·13·(1/4) = 13/2`.

The missing P7 content is the lana shell-defect cancellation (VcI.lean green),
not the coefficient identity. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7CalibrationActual

/-- A763 paper coefficient `c_V = 1/4`. -/
def cVModel : ℝ := 1 / 4

theorem cVModel_eq : cVModel = 1 / 4 := rfl

/-- Closed form of `sFactor((ℓ−1)/2) = ℓ(ℓ+1)/12` (real ℓ). -/
def sFactorClosed (l : ℝ) : ℝ := l * (l + 1) / 12

/-- A763 calibration: `sFactor = ((ℓ+1)/6)·(2ℓ·c_V)`. -/
theorem sFactorClosed_eq_ratio_mul_two_l_cV (l : ℝ) :
    sFactorClosed l = ((l + 1) / 6) * (2 * l * cVModel) := by
  unfold sFactorClosed cVModel
  ring

/-- Equivalent direct form: `sFactor = ℓ(ℓ+1)/12`. -/
theorem sFactorClosed_eq (l : ℝ) : sFactorClosed l = l * (l + 1) / 12 := rfl

/-- lana coefficient `c_lana = (sFactor−1)/(2ℓ)`. -/
def cLana (l : ℝ) : ℝ := (sFactorClosed l - 1) / (2 * l)

/-- Definitional P7 identity: `sFactor − 1 = 2ℓ·c_lana`. -/
theorem sFactor_sub_one_eq_two_l_mul_cLana (l : ℝ) (hl : l ≠ 0) :
    sFactorClosed l - 1 = 2 * l * cLana l := by
  unfold cLana
  field_simp [hl]

/-- A963 calibration numeric check at `ℓ = 13`: `sFactor = 91/6`. -/
theorem sFactorClosed_13 : sFactorClosed 13 = 91 / 6 := by
  unfold sFactorClosed
  norm_num

/-- At `ℓ = 13`, `sFactor−1 = 85/6` but `2ℓ·c_V = 13/2`; hence
`sFactor−1 = 2ℓ·c_V` is FALSE. -/
theorem calibration_not_sub_one (h : (85 / 6 : ℝ) = 13 / 2) : False :=
  by norm_num at h

/-- The correct calibrated form at `ℓ = 13`: `sFactor = ((14)/6)·(2·13·(1/4))`. -/
theorem calibration_13 : (91 / 6 : ℝ) = ((13 + 1) / 6) * (2 * 13 * (1 / 4)) := by
  norm_num

def p7Rows : List (String × String × String) :=
  [ ("c_V", "c_V = 1/4 (A763)", "DEF (cVModel)"),
    ("sFactor closed form", "sFactor(nC) = ℓ(ℓ+1)/12 for nC=(ℓ−1)/2", "DEF (sFactorClosed)"),
    ("calibrated identity", "sFactor = ((ℓ+1)/6)·(2ℓ c_V)", "PROVED (sFactorClosed_eq_ratio_mul_two_l_cV)"),
    ("lana coefficient", "sFactor−1 = 2ℓ·c_lana with c_lana=(sFactor−1)/(2ℓ)", "PROVED (sFactor_sub_one_eq_two_l_mul_cLana)"),
    ("false identity", "sFactor−1 = 2ℓ·c_V is FALSE (ℓ=13: 85/6 vs 13/2)", "REFUTED (calibration_not_sub_one / calibration_13)"),
    ("P7 remaining", "lana shell-defect/tame cancellation (VcI.lean shellExcess_eq_tame etc.), not the coefficient identity", "GAP (lana green cited)") ]

theorem p7Rows_length : p7Rows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7CalibrationActual.sFactorClosed_eq_ratio_mul_two_l_cV
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7CalibrationActual.sFactor_sub_one_eq_two_l_mul_cLana
#print axioms LeanFormal.IUT.XiFPaper.Mzk1P7CalibrationActual.calibration_13

end LeanFormal.IUT.XiFPaper.Mzk1P7CalibrationActual

end