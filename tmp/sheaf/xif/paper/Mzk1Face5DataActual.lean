/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaCancelActual
import tmp.sheaf.xif.paper.Mzk1PaperNormDeficitActual
import tmp.sheaf.xif.paper.Mzk1ArchTorsionDictionaryActual
import tmp.sheaf.xif.paper.Mzk1RDefinitionAuditV2Actual

/-! # A907 hull: face5 per-place decomposition data

Per-place coefficient logMuPaper p e r n = (1 + [p=2] - 1/e - r/n) log p.
Faithful candidates nonnegative: faithful_coeffs_nonneg (5 places);
odd/2-adic lower bounds logMuPaper_ge_odd / _ge_two.
Arch: archConstant = log(sqrt 2 * pi), archConstant_eq_log, archConstant_nonneg.
Exact identity (theta cancellation), l = 2k+1:
  (sumLogMu + thetaSumPaper k l A) - ssCoeff(l)*A = sumLogMu,
since thetaSumPaper = clana*A and clana = ssCoeff at l = 2k+1.
Thus face5 V - (sF-1)A = sumLogMu (when V = sumLogMu+theta). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaCancelActual
open LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1RDefinitionAuditV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open scoped BigOperators

/-- Faithful candidate coefficients are nonnegative (re-export). -/
theorem face5_faithful_nonneg :
    0 <= paperMuCoeff 2 1 1 1 ∧ 0 <= paperMuCoeff 2 1 1 4 ∧
    0 <= paperMuCoeff 3 2 1 2 ∧ 0 <= paperMuCoeff 5 4 1 4 ∧
    0 <= paperMuCoeff 11 1 0 1 :=
  faithful_coeffs_nonneg

/-- Arch constant is nonnegative. -/
theorem archConstant_nonneg : 0 <= archConstant := by
  rw [archConstant_eq]
  have h1 : 0 <= Real.log 2 / 2 := by
    have : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : 0 <= Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-- Face5 V: sumLogMu + theta part. -/
noncomputable def face5V (sumLogMu theta : ℝ) : ℝ := sumLogMu + theta

/-- Exact face5 decomposition: for l = 2k+1, k >= 2,
(sumLogMu + thetaSumPaper k l A) - ssCoeff(l)*A = sumLogMu. -/
theorem face5_decomposition (k : Nat) (hk : 2 <= k) (A sumLogMu : ℝ) :
    face5V sumLogMu (thetaSumPaper k (2 * (k : ℝ) + 1) A) -
        Mzk1LargeLTheoremActual.ssCoeff (2 * (k : ℝ) + 1) * A = sumLogMu := by
  unfold face5V
  rw [thetaSumPaper_eq_clana_mul k (by omega) (2 * (k : ℝ) + 1) A,
    clana_eq_ssCoeff k hk]
  ring

/-- Deficit form: the deficit is -sumLogMu (re-export of theta cancellation). -/
theorem face5_deficit_eq (k : Nat) (hk : 2 <= k) (A sumLogMu : ℝ) :
    paperDeficit (Mzk1LargeLTheoremActual.ssCoeff (2 * (k : ℝ) + 1)) A sumLogMu
        (thetaSumPaper k (2 * (k : ℝ) + 1) A) = -sumLogMu :=
  paperDeficit_cancel_thetaSum k hk A sumLogMu

/-- If the per-place sumLogMu part is nonnegative, the face5 deficit is nonpositive. -/
theorem face5_deficit_nonpos (k : Nat) (hk : 2 <= k) (A sumLogMu : ℝ)
    (h : 0 <= sumLogMu) :
    paperDeficit (ssCoeff (2 * (k : ℝ) + 1)) A sumLogMu
        (thetaSumPaper k (2 * (k : ℝ) + 1) A) <= 0 :=
  paperDeficit_nonpos_of_sum_nonneg k hk A sumLogMu h

def face5Rows : List (String × String × String) :=
  [ ("logMuPaper", "(1+[p=2]-1/e-r/n) log p", "DEF (Mzk1PaperNormMuActual)"),
    ("faithful coeff nonneg", "5 candidate places", "PROVED (faithful_coeffs_nonneg)"),
    ("odd/2-adic lower", "logMuPaper >= base", "PROVED (logMuPaper_ge_odd/_ge_two)"),
    ("arch constant", "log(sqrt2*pi) = log2/2+log pi >= 0", "PROVED (archConstant_nonneg)"),
    ("face5 V", "sumLogMu + theta", "DEF (face5V)"),
    ("decomposition", "V - ssCoeff*A = sumLogMu at l=2k+1", "PROVED (face5_decomposition)"),
    ("deficit", "deficit = -sumLogMu; nonpos if sumLogMu>=0", "PROVED (face5_deficit_eq/_nonpos)") ]

theorem face5Rows_length : face5Rows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual.archConstant_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual.face5_decomposition
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual.face5_deficit_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual.face5_deficit_nonpos

end LeanFormal.IUT.XiFPaper.Mzk1Face5DataActual

end