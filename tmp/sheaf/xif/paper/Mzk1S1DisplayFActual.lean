import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1S1DisplayFActual — correct F-version of the Thm 1.10 display

The existing thm110_final_display_F in S3171 has a tautological hF hypothesis;
this file supplies the honest F-bound: if the F_tpd logs are dominated by the F logs
and the coefficient (1 + 20 d_mod/l) is nonnegative, the display's right side with
F logs bounds the same left side.  This is the paper Step (ii) dictionary step as an
explicit hypothesis; no closure claim; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-- Correct F-bound: display + F log domination + nonnegative coefficient. -/
theorem thm110_final_display_F_bound (T : Thm110DisplayTerms)
    (H : Thm110DisplayInputs T) (logDF logFF : Real)
    (hcoef : 0 ≤ 1 + 20 * T.dmod / T.l)
    (hsumle : T.logDFpd + T.logFFpd ≤ logDF + logFF) :
    thm110Lhs T ≤ (1 + 20 * T.dmod / T.l) * (logDF + logFF) +
      20 * (T.eStar * T.l + T.etaPrm) := by
  have hmain := thm110_final_display T H
  unfold thm110Rhs at hmain
  have hcoef' : 0 ≤ 1 + 20 * T.dmod / T.l := hcoef
  have hmul := mul_le_mul_of_nonneg_left hsumle hcoef'
  linarith

/-- Rows: F-version status. -/
def s1DisplayFRows : List (String × String × String) :=
  [ ("display (F_tpd)", "thm110_final_display (core, conditional)", "PROVED (conditional)"),
    ("F-bound Step (ii)", "thm110_final_display_F_bound", "PROVED (conditional: log domination + nonnegative coefficient)"),
    ("named inputs", "Thm110DisplayInputs (hCor312/hSlack) remain named", "NAMED"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem s1DisplayFRows_length : s1DisplayFRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual

end
