/- R2/C4 wiring: paper Theta upper bound -> C4 scalar consumer -1 <= CTheta.
   Composition of the retarget consumer with an explicit paper-Theta upper (hTheta).
   No fake equality; q-ray inputs explicit. -/
import tmp.sheaf.xif.paper.Mzk1CThetaRetargetActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual

/-- R2 -> C4: a paper-Theta upper bound (theta <= CThetaPaper * A) plus q-ray data
    implies the C4 scalar lower bound -1 <= CTheta. -/
theorem cTheta_ge_neg_one_of_paperTheta_le
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {thetaLogVolume qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hTheta : thetaLogVolume ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm :=
  CTheta_ge_neg_one_of_upper_CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm
    hq hincl habs hTheta hA hB

#print axioms cTheta_ge_neg_one_of_paperTheta_le

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual
