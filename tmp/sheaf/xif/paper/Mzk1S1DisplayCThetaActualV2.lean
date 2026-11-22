import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.Mzk1Thm110SlackActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1S1DisplayCThetaActualV2 — S1.display: real CThetaPaper lower bound -> display

DAG node: iutiv-abc:IUTIV.S1.display (CONDITIONAL, 0 unproved deps).
S2715CThetaPaperScaleActual identifies -1 <= CThetaPaper exactly with the bracket
inequality of Thm 1.10; algebraically that bracket inequality is exactly the hCor312
field of Thm110DisplayInputs (lhs <= mid + cor312Gap).  This file proves that
equivalence-directed consumer, and combines it with the explicit logQ bound that
discharges hSlack (Mzk1Thm110SlackActual), yielding the exact Thm 1.10 display from
a real CThetaPaper lower bound plus the explicit numeric logQ hypothesis.

No closure claim: CThetaPaper >= -1 and the logQ bound remain explicit inputs.
GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual

/-- The paper-scale CThetaPaper lower bound gives the hCor312 field of the display. -/
theorem hCor312_of_CThetaPaper_ge_neg_one (T : Thm110DisplayTerms)
    (l : PrimeGeFive) (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ CThetaPaper l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm) :
    thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T := by
  have hbracket := (CThetaPaper_ge_neg_one_iff l T.logQ T.dmod dFpd fFpd
    T.eStar T.etaPrm hlogQ).mp hC
  have hbracket' : (1 / 6) * (1 - 12 / (T.l) ^ 2) * T.logQ ≤ thm110Mid T := by
    rw [hL]
    rw [← hD, ← hF] at hbracket
    simpa [thm110Mid, hL] using hbracket
  have hgap : thm110Lhs T - thm110Cor312Gap T =
      (1 / 6) * (1 - 12 / (T.l) ^ 2) * T.logQ := by
    unfold thm110Lhs thm110Cor312Gap
    field_simp
  linarith

/-- Exact Thm 1.10 display from a real CThetaPaper lower bound plus the explicit
logQ bound (hSlack discharged); hCor312 is derived, not assumed. -/
theorem thm110_final_display_of_CThetaPaper_logQ (T : Thm110DisplayTerms)
    (l : PrimeGeFive) (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ CThetaPaper l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display_of_logQ_bound T
    (hCor312_of_CThetaPaper_ge_neg_one T l dFpd fFpd hL hD hF hlogQ hC)
    hl hd hsum he hQ

/-- Rows: S1.display consumer status. -/
def s1DisplayCThetaRows : List (String × String × String) :=
  [ ("CThetaPaper >= -1 -> hCor312", "hCor312_of_CThetaPaper_ge_neg_one (S2715 equivalence)", "PROVED"),
    ("explicit logQ bound -> display", "thm110_final_display_of_CThetaPaper_logQ", "PROVED (conditional)"),
    ("named inputs", "CThetaPaper >= -1; explicit logQ bound", "NAMED/EXPLICIT (not proved)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem s1DisplayCThetaRows_length : s1DisplayCThetaRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2

end
