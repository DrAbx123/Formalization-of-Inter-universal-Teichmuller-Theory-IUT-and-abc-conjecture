import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1F4bFiniteProofActual — f4b finite step facts, proved

Genuine closure of the finite-part f4b statements using the existing tree
lemmas: the step target does not increase max degree and, on the stable
max-degree branch, strictly decreases the maximal count.
No closure of the P1 geometric transport; no sorry/axiom; gate NOT PASSED;
registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1F4bFiniteProofActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

theorem finiteMaxDegTransfer_proved (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) ≤ maxDeg S :=
  maxDeg_stepSet_le S alpha0 halpha0 hmax

theorem finiteNumMaxStrict_proved (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) (h2 : 2 ≤ degQ alpha0)
    (hsame : maxDeg (stepSet S alpha0) = maxDeg S) :
    numMax (stepSet S alpha0) < numMax S :=
  numMax_stepSet_lt S alpha0 halpha0 hmax h2 hsame

theorem finiteMeasureStrict_proved (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) (h2 : 2 ≤ degQ alpha0) :
    Prod.Lex (· < ·) (· < ·)
      (maxDeg (stepSet S alpha0), numMax (stepSet S alpha0))
      (maxDeg S, numMax S) :=
  measure_stepSet_lt S alpha0 halpha0 hmax h2

end LeanFormal.IUT.XiFPaper.Mzk1F4bFiniteProofActual

end
