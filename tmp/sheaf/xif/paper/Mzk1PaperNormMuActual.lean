/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A795 hull: paper-normalized `log mu(I_v)` and A/B bounds

Paper normalization (ROUTES §6.1):

  `logMuPaper_v = (1 + [p=2] - 1/e_v - r_v/n_v) * log p_v`.

The A/B exponents of `IntegralLogShellSharpBounds` control the residue-card
correction: green
* `logShellPaperExponent_sum_mul_log_le_three_add_log`
  `(A+B) log p <= 3 + log e`;
* `logShellPaperAExponent_sub_inv_mul_log_le_two`
  `(A - 1/e) log p <= 2`;
* `logShellPaperBExponent_add_inv_mul_log_le_one_add_log`
  `(B + 1/e) log p <= 1 + log e`.

Elementary bounds proved here:
* odd p: `(1 - 1/e - r/n) log p <= logMuPaper`;
* p=2: `(2 - 1/e - r/n) log p <= logMuPaper`;
* upper (r/n >= 0): `logMuPaper <= (1 + [p=2]) log p`.

Per-place verdict: the paper-normalized inequality is
`(sFactor-1)A <= sum_v logMuPaper_v + (scaled theta correction)`; it is
equivalent to the per-place target `A_v <= Lbar_v + Dbar_v` only after the
index/diff dictionary; A/B gives bounds, not the missing Szpiro-type term. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

def paperMuCoeff (p e r n : ℝ) : ℝ :=
  1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n

def logMuPaper (p e r n : ℝ) : ℝ := paperMuCoeff p e r n * Real.log p

theorem logMuPaper_eq (p e r n : ℝ) :
    logMuPaper p e r n =
      (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p := rfl

/-- Odd-p lower bound. -/
theorem logMuPaper_ge_odd (p e r n : ℝ) (hp2 : p ≠ 2) (hlog : 0 ≤ Real.log p) :
    (1 - 1 / e - r / n) * Real.log p ≤ logMuPaper p e r n := by
  unfold logMuPaper paperMuCoeff
  rw [if_neg hp2]
  nlinarith

/-- `p=2` lower bound. -/
theorem logMuPaper_ge_two (p e r n : ℝ) (hp2 : p = 2) (hlog : 0 ≤ Real.log p) :
    (2 - 1 / e - r / n) * Real.log p ≤ logMuPaper p e r n := by
  unfold logMuPaper paperMuCoeff
  rw [if_pos hp2]
  nlinarith

/-- Upper bound when `r/n >= 0`. -/
theorem logMuPaper_le_base (p e r n : ℝ) (hlog : 0 ≤ Real.log p)
    (he : 0 ≤ 1 / e) (hrn : 0 ≤ r / n) :
    logMuPaper p e r n ≤
      (1 + (if p = 2 then 1 else 0 : ℝ)) * Real.log p := by
  unfold logMuPaper paperMuCoeff
  nlinarith

/-- Per-place paper-normalized verdict (framework): if the paper `logMuPaper`
lower bounds sum to at least the SSIneq coefficient times `A`, the paper
inequality holds; otherwise the difference is exactly the missing term. -/
def PaperNormVerdict (ssCoeff A sumLogMu sumTheta : ℝ) : Prop :=
  ssCoeff * A ≤ sumLogMu + sumTheta

theorem paperNormVerdict_iff (ssCoeff A sumLogMu sumTheta : ℝ) :
    PaperNormVerdict ssCoeff A sumLogMu sumTheta ↔
      ssCoeff * A ≤ sumLogMu + sumTheta := Iff.rfl

/-- If the verdict fails, the exact deficit is `ssCoeff*A - (sumLogMu+sumTheta)`. -/
def paperNormDeficit (ssCoeff A sumLogMu sumTheta : ℝ) : ℝ :=
  ssCoeff * A - (sumLogMu + sumTheta)

theorem paperNormVerdict_iff_deficit_nonpos (ssCoeff A sumLogMu sumTheta : ℝ) :
    PaperNormVerdict ssCoeff A sumLogMu sumTheta ↔
      paperNormDeficit ssCoeff A sumLogMu sumTheta ≤ 0 := by
  unfold PaperNormVerdict paperNormDeficit
  constructor <;> intro h <;> linarith

def paperNormRows : List (String × String × String) :=
  [ ("paper log mu", "logMuPaper = (1+[p=2]-1/e-r/n)log p", "DEF"),
    ("odd lower", "(1-1/e-r/n)log p <= logMuPaper", "PROVED (logMuPaper_ge_odd)"),
    ("p=2 lower", "(2-1/e-r/n)log p <= logMuPaper", "PROVED (logMuPaper_ge_two)"),
    ("upper", "logMuPaper <= (1+[p=2])log p when r/n>=0", "PROVED (logMuPaper_le_base)"),
    ("A/B bounds", "(A+B)logp<=3+loge; (A-1/e)logp<=2; (B+1/e)logp<=1+loge", "GREEN (IntegralLogShellSharpBounds; cited)"),
    ("per-place verdict", "PaperNormVerdict ssCoeff A sumLogMu sumTheta := ssCoeff*A <= sumLogMu+sumTheta", "DEF + equivalence"),
    ("deficit", "deficit = ssCoeff*A - (sumLogMu+sumTheta); holds iff deficit<=0", "PROVED (paperNormVerdict_iff_deficit_nonpos)"),
    ("gap", "identify sumTheta with the scaled theta procession term (c_lana=(sFactor-1)/(2l)) and sumLogMu with index+diff; A/B alone does not prove the verdict", "GAP") ]

theorem paperNormRows_length : paperNormRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.logMuPaper_ge_odd
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.logMuPaper_le_base
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.paperNormVerdict_iff_deficit_nonpos

end LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

end