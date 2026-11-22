import tmp.sheaf.xif.paper.Mzk1Thm110SlackActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5DisplaySlackActual — E-5 display consumer with explicit logQ bound

DAG node: e-deep:E5.display (CONDITIONAL, 2 unproved deps).  Combines:
* the exact Thm 1.10 display with hSlack replaced by the explicit logQ bound
  (Mzk1Thm110SlackActual), and
* the (b)/(c) undilated-interface ABC consumer (S3171IUTIVSection1DisplayActual).
This is a conditional consumer; hCor312 and the logQ bound remain explicit inputs.
No closure claim; gate NOT PASSED. Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5DisplaySlackActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

/-- Thm 1.10 display from hCor312 + explicit logQ bound (hSlack discharged). -/
theorem thm110_final_display_of_logQ_slack (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    thm110Lhs T ≤ thm110Rhs T :=
  LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual.thm110_final_display_of_logQ_bound T
    hCor312 hl hd hsum he hQ

/-- Combined consumer: display (with explicit slack bound) and ABC from the two
undilated (b)/(c) interfaces. -/
theorem thm110_display_and_abc_of_logQ_bound {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm))
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  ⟨thm110_final_display_of_logQ_slack T hCor312 hl hd hsum he hQ,
   abcConjecture_of_undilated hb hc⟩

/-- Rows: E-5 display consumer status. -/
def e5DisplaySlackRows : List (String × String × String) :=
  [ ("Thm 1.10 display", "thm110_final_display_of_logQ_bound", "PROVED (conditional: hCor312 + explicit logQ bound)"),
    ("(b)/(c) -> ABC", "abcConjecture_of_undilated (existing)", "PROVED (conditional)"),
    ("combined consumer", "thm110_display_and_abc_of_logQ_bound", "PROVED (conditional)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5DisplaySlackRows_length : e5DisplaySlackRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5DisplaySlackActual

end
