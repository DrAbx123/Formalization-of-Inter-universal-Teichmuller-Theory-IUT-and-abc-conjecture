/- Exact instantiation H := CThetaPaper * paperQAbsLog of the final C4 consumer.
   Once R2 supplies paperTheta <= CThetaPaper * paperQAbsLog (hR2), and the q-ray
   inputs hold, C4 gives -1 <= CTheta. No extra H variable, no fake equality. -/
import tmp.sheaf.xif.paper.Mzk1ULCThetaFinalConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaR2InstantiationActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalConsumerActual

/-- Exact instantiation: paperTheta <= CThetaPaper * paperQAbsLog gives -1 <= CTheta. -/
theorem cTheta_ge_neg_one_of_paperTheta_le_CThetaPaper
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {paperTheta qParameter : Real}
    (hR2 : paperTheta ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ paperTheta)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm :=
  cTheta_ge_neg_one_of_R2_readout l logQ dmod dFpd fFpd eStar etaPrm
    (H := CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    hR2 rfl hq hincl habs hA hB

#print axioms cTheta_ge_neg_one_of_paperTheta_le_CThetaPaper

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaR2InstantiationActual
