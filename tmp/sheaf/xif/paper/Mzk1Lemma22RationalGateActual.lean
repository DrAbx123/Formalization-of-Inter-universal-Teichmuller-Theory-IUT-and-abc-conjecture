import tmp.sheaf.xif.paper.Mzk1Lemma22BaseGoodActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StepProviderProofActual
import tmp.sheaf.xif.paper.Mzk1Lemma22InductionProofActual
import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import Mathlib.Tactic

/-! # Mzk1Lemma22RationalGateActual — UNCONDITIONAL rational 2.2 gate (F=Q component)

STEP 0 prior-art: reuse Mzk1Lemma22BaseGoodActual (baseGood_exists PROVED), 
Mzk1Lemma22StepProviderProofActual (stepProvider_holds + conditional induction),
Mzk1Lemma22InductionProofActual (mzk1Lemma22_induction_conditional), 
Mzk1Lemma22CritValueActual + Mzk1CritValueInImageProofActual (image-based CV-in-image),
stepxi RestatedLemma22InterfaceActual (Mzk1Lemma22InductionStatement/Mzk1Lemma22Target/
target_of_induction).

SCOPE (Lead A311-A319): this is the RATIONAL (P1Point Q) component of paper Lemma 2.2.
The algebraic-input (P1Point Qbar) / m-d nested induction is a separate NAMED reduction
layer; this file does NOT claim paper 2.2/2.4 closure.  Gate NOT PASSED; binding HOLD.

INTEGRITY NOTE (Lead A356; 谢德 re-audit): the proven chain uses the UNCHANGED stepxi
Good (C-point condition: aeval z f ∉ {0,1} -> aeval z f.derivative ≠ 0).  The unnormalized gPoly
does NOT satisfy the literal 0/1 critical-value statement (refuted in Mzk1CritValueInImageProofActual);
intermediate steps use the IMAGE-BASED CritValueInImageStatement, and the composite's C-point
condition is derived via the two chain-rule cases.  Base f = C c * X satisfies it vacuously
(derivative = C c ≠ 0).  Mzk1BaseProviderProofActual (sorryAx) is NOT used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22RationalGateActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseGoodActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepProviderProofActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open Polynomial

/-- BaseProviderStatement is PROVED by the baseGood file. -/
theorem baseProvider_holds : BaseProviderStatement :=
  fun S β hcard H => baseGood_exists S β H hcard

/-- UNCONDITIONAL rational induction statement (StepProvider PROVED + base PROVED). -/
theorem mzk1Lemma22_inductionStatement_rational : Mzk1Lemma22InductionStatement :=
  mzk1Lemma22_induction_of_base baseProvider_holds

/-- UNCONDITIONAL restated 2.2 target over Q (F=Q component). -/
theorem mzk1Lemma22_target_rational (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) : Mzk1Lemma22Target S β :=
  target_of_induction mzk1Lemma22_inductionStatement_rational S β H

def rationalGateRows : List (String × String × String) :=
  [ ("base provider |S|<=3 Good", "PROVED", "Mzk1Lemma22BaseGoodActual.baseGood_exists (C c*X)")
  , ("step provider + image-based CV", "PROVED", "Mzk1Lemma22StepProviderProofActual.stepProvider_holds")
  , ("rational induction statement", "PROVED", "mzk1Lemma22_inductionStatement_rational")
  , ("rational restated 2.2 target", "PROVED", "mzk1Lemma22_target_rational")
  , ("scope", "F=Q COMPONENT", "Qbar / m-d nested induction = named reduction layer (out of gate)")
  , ("closure", "NOT CLAIMED", "paper 2.2/2.4 not complete; binding HOLD") ]

theorem rationalGateRows_length : rationalGateRows.length = 6 := rfl

#check mzk1Lemma22_inductionStatement_rational
#check mzk1Lemma22_target_rational

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22RationalGateActual
end
