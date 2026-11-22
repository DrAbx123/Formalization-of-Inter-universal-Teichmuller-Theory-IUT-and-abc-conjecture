/- CTheta P6 consumer: wire CThetaPaper lower bound to P6 final display.
   (1) cThetaP6_lower: R0/R1/R2-style upper data (as in CTheta_ge_neg_one_of_upper_CThetaPaper,
       explicit hypotheses) => -1 <= CTheta (paper/l); cite route 4.5, IV L1365-1376.
   (2) p6_final_of_CThetaPaper: given -1 <= CThetaPaper and Thm110DisplayTerms compat data,
       apply Mzk1S1DisplayCThetaActualV2.hCor312_of_CThetaPaper_ge_neg_one.
   No fake equality CThetaPaper = thetaLogVolume/M. -/
import tmp.sheaf.xif.paper.Mzk1CThetaRetargetActual
import tmp.sheaf.xif.paper.Mzk1S1DisplayCThetaActualV2
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaP6ConsumerActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2

/-- (1) Retarget lower bound: upper data for CThetaPaper*A => -1 <= CTheta. -/
theorem cThetaP6_lower (l : PrimeGeFive)
    (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {thetaLogVolume qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hupper : thetaLogVolume ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm :=
  CTheta_ge_neg_one_of_upper_CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm
    hq hincl habs hupper hA hB

/-- (2) P6 consumer: CThetaPaper lower bound gives the final display inequality. -/
theorem p6_final_of_CThetaPaper (T : Thm110DisplayTerms) (l : PrimeGeFive)
    (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ CThetaPaper l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm) :
    thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T :=
  hCor312_of_CThetaPaper_ge_neg_one T l dFpd fFpd hL hD hF hlogQ hC

#print axioms cThetaP6_lower
#print axioms p6_final_of_CThetaPaper

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaP6ConsumerActual