import tmp.sheaf.xif.paper.Mzk1S1DisplayCThetaActualV2
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5CThetaABCActualV4 — combined CThetaPaper display + (b)/(c) ABC consumer

DAG nodes: iutiv-abc:IUTIV.S1.display / e-deep:E5.display.  Combines the exact
Thm 1.10 display (from a real CThetaPaper lower bound plus explicit logQ bound) with
the (b)/(c) undilated-interface ABC route.  All inputs remain explicit/named.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5CThetaABCActualV4

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

universe u

theorem thm110_display_and_abc_of_CThetaPaper_logQ {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (T : Thm110DisplayTerms) (l : PrimeGeFive) (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ CThetaPaper l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm))
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  ⟨thm110_final_display_of_CThetaPaper_logQ T l dFpd fFpd hL hD hF hlogQ hC
      hl hd hsum he hQ,
   abcConjecture_of_undilated hb hc⟩

/-- Rows: combined consumer status. -/
def e5CThetaRowsV4 : List (String × String × String) :=
  [ ("display from CThetaPaper + logQ", "thm110_final_display_of_CThetaPaper_logQ (S1 V2)", "PROVED (conditional)"),
    ("(b)+(c) -> ABC", "abcConjecture_of_undilated", "PROVED (conditional)"),
    ("combined consumer", "thm110_display_and_abc_of_CThetaPaper_logQ", "PROVED (conditional)"),
    ("scope", "named inputs explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5CThetaRowsV4_length : e5CThetaRowsV4.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5CThetaABCActualV4

end
