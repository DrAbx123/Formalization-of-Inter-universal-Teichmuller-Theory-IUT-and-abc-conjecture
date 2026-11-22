/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A790 hull: lower bounds for the paper shell volume `log mu(I_v)`

Paper normalization (ROUTES §6.1): `log mu = (1+[p=2]-1/e-r/n)*log p`.
Green A/B exponents from `IntegralLogShellSharpBounds` bound the residue-card
exponent of `logShellIntegerIndex`; here we record the elementary lower bounds
for `log mu` used by the per-place inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PerPlaceBoundHullActual

def paperShellLogMu (p e r n : ℝ) : ℝ :=
  (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p

theorem paperShellLogMu_ge_lower (p e r n : ℝ) (hlog : 0 ≤ Real.log p) :
    (1 - 1 / e - r / n) * Real.log p ≤ paperShellLogMu p e r n := by
  unfold paperShellLogMu
  have h2 : 0 ≤ (if p = 2 then 1 else 0 : ℝ) := by split_ifs <;> norm_num
  nlinarith

theorem paperShellLogMu_ge_lower_two (p e r n : ℝ) (hlog : 0 ≤ Real.log p)
    (hp2 : p = 2) :
    (2 - 1 / e - r / n) * Real.log p ≤ paperShellLogMu p e r n := by
  unfold paperShellLogMu
  rw [if_pos hp2]
  nlinarith

/-- Per-place inequality reduction: a lower bound `L` for `log mu` and the
arithmetic bound `qcoef <= L + (1 - 1/(2l))*logIdx` imply the target inequality
`qcoef <= log mu + (1 - 1/(2l))*logIdx` (the form with `diff = log mu - logIdx/(2l)`). -/
theorem perPlace_inequality_of_mu_lower
    (qcoef logIdx logMu L l : ℝ) (hmu : L ≤ logMu)
    (h : qcoef ≤ L + (1 - 1 / (2 * l)) * logIdx) :
    qcoef ≤ logMu + (1 - 1 / (2 * l)) * logIdx := by
  linarith

/-- The same with `diff = log mu - (1/(2l))*logIdx`: the target is
`qcoef <= logIdx + diff`. -/
theorem perPlace_inequality_of_mu_lower_diff
    (qcoef logIdx logMu diff L l : ℝ) (hmu : L ≤ logMu)
    (hdiff : diff = logMu - (1 / (2 * l)) * logIdx)
    (h : qcoef ≤ L + (1 - 1 / (2 * l)) * logIdx) :
    qcoef ≤ logIdx + diff := by
  rw [hdiff]
  linarith

def perPlaceRows : List (String × String × String) :=
  [ ("paper mu", "log mu = (1+[p=2]-1/e-r/n)*log p", "DEF"),
    ("odd p lower", "log mu >= (1-1/e-r/n)*log p", "PROVED (paperShellLogMu_ge_lower)"),
    ("p=2 lower", "log mu >= (2-1/e-r/n)*log p", "PROVED (paperShellLogMu_ge_lower_two)"),
    ("A/B exponents", "logShellPaperAExponent/BExponent + logShellPaperExponent_sum_mul_log_le_three_add_log", "GREEN (IntegralLogShellSharpBounds, cited)"),
    ("per-place reduction", "qcoef <= L + (1-1/(2l))logIdx and L <= log mu => qcoef <= logIdx + diff", "PROVED (perPlace_inequality_of_mu_lower_diff)"),
    ("remaining", "instantiate qcoef=(f/([F:Q]*2l))logp and prove arithmetic bound with exponent>=1, f>=1, A/B", "abc arithmetic (A790 joint)") ]

theorem perPlaceRows_length : perPlaceRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PerPlaceBoundHullActual.paperShellLogMu_ge_lower
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PerPlaceBoundHullActual.perPlace_inequality_of_mu_lower_diff

end LeanFormal.IUT.XiFPaper.Mzk1PerPlaceBoundHullActual

end