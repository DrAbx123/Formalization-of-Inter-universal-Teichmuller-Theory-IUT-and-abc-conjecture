import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Thm110SlackActual — IUT IV Thm 1.10: hSlack replaced by an explicit numeric bound

DAG node: iutiv-abc:IUTIV.S1.display (CONDITIONAL, 0 unproved deps).
The display file leaves two named inputs: hCor312 and hSlack.  Here the *slack* input
hSlack : thm110Cor312Gap T <= thm110Rhs T - thm110Mid T is replaced by an explicit,
checkable numeric bound on logQ:

  logQ <= 4*dmod*l*(logDFpd+logFFpd) + 5*l^2*(eStar*l+etaPrm)

Under the paper's nonnegativity hypotheses (l>0, dmod>=0, sums>=0), this implies hSlack
by elementary arithmetic (the (1+6)/l gap is 2/l^2).  hCor312 remains the only named
paper input of the display.  This is a conditional reduction, not a proof of hCor312 or
of the paper's Step (v); no closure claim; gate NOT PASSED.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual

open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-- The slack input is exactly the numeric inequality of the display. -/
theorem thm110Slack_iff (T : Thm110DisplayTerms) :
    (thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T) ↔
      thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T := Iff.rfl

/-- **Explicit logQ bound implies the paper's slack step.** -/
theorem thm110Slack_of_logQ_bound (T : Thm110DisplayTerms)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T := by
  unfold thm110Cor312Gap thm110Rhs thm110Mid
  have hlne : T.l ≠ 0 := ne_of_gt hl
  have hR : (1 + 20 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        20 * (T.eStar * T.l + T.etaPrm) -
        ((1 + 12 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
          10 * (T.eStar * T.l + T.etaPrm)) =
      (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) := by
    field_simp
    ring
  rw [hR]
  have hG : (1 / 6) * (12 / T.l ^ 2) * T.logQ = (2 / T.l ^ 2) * T.logQ := by
    field_simp
    ring
  rw [hG]
  have hpos : 0 < 2 / T.l ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hQ (le_of_lt hpos)
  have hcalc : (2 / T.l ^ 2) *
        ((4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
          5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) =
      (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) := by
    field_simp
    ring
  calc (2 / T.l ^ 2) * T.logQ
      ≤ (2 / T.l ^ 2) *
          ((4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
            5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) := hmul
    _ = (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) := hcalc

/-- **Display inputs from hCor312 + explicit logQ bound** (hSlack discharged to a
checkable numeric inequality). -/
theorem thm110DisplayInputs_of_logQ_bound (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    Thm110DisplayInputs T :=
  ⟨hCor312, thm110Slack_of_logQ_bound T hl hd hsum he hQ⟩

/-- The exact display follows from hCor312 plus the explicit logQ bound. -/
theorem thm110_final_display_of_logQ_bound (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display T
    (thm110DisplayInputs_of_logQ_bound T hCor312 hl hd hsum he hQ)

/-- Honest rows: what is discharged and what remains named. -/
def thm110SlackRows : List (String × String × String) :=
  [ ("display shape", "thm110_final_display (exact Step (v) shape)", "PROVED CONDITIONALLY"),
    ("hCor312", "thm110Lhs <= thm110Mid + thm110Cor312Gap", "NAMED paper input (unchanged)"),
    ("hSlack", "thm110Slack_of_logQ_bound: replaced by explicit logQ bound under nonnegativity", "REDUCED TO CHECKABLE NUMERIC BOUND"),
    ("explicit logQ bound", "logQ <= 4*dmod*l*sum + 5*l^2*(eStar*l+etaPrm)", "EXPLICIT HYPOTHESIS (not proved)"),
    ("scope", "conditional reduction only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem thm110SlackRows_length : thm110SlackRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual

end
