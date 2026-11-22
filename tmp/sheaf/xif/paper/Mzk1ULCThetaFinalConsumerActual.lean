/- Final consumer: once R2 supplies paperTheta <= H (paper Theta weighted-average readout),
   with H = CThetaPaper * paperQAbsLog and the q-ray inputs, C4 gives -1 <= CTheta.
   The R2 theorem itself (rowPackets_weightedAverage_le_H, owner kurt) is not imported here;
   its conclusion is passed as hR2 at the same theta scalar. No fake equality. -/
import tmp.sheaf.xif.paper.Mzk1ULCThetaC4HWiringActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalConsumerActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual

/-- Final C4 consumer from the R2 paper-Theta readout paperTheta <= H. -/
theorem cTheta_ge_neg_one_of_R2_readout
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {paperTheta H qParameter : Real}
    (hR2 : paperTheta ≤ H)
    (hH : H = CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ paperTheta)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm :=
  cTheta_ge_neg_one_of_H_readout l logQ dmod dFpd fFpd eStar etaPrm
    hq hincl habs hR2 hH hA hB

#print axioms cTheta_ge_neg_one_of_R2_readout

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalConsumerActual
