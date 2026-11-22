/- Wire R2's paperTheta readout (thetaLogVolume <= H) to the C4 scalar consumer.
   Once R2 gives paperThetaWeighted_le_H with H = CThetaPaper * paperQAbsLog, this
   composition yields -1 <= CTheta. The R2 side is passed as the explicit hypothesis
   hThetaH (same theta scalar); no re-editing of kurt's RowPacketWiring file. -/
import tmp.sheaf.xif.paper.Mzk1ULCThetaC4ComposeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual

/-- R2 readout -> C4: if the paper Theta readout theta satisfies theta <= H and
    H = CThetaPaper * paperQAbsLog, and the q-ray inputs hold, then -1 <= CTheta. -/
theorem cTheta_ge_neg_one_of_H_readout
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {thetaLogVolume qParameter H : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hThetaH : thetaLogVolume ≤ H)
    (hH : H = CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm :=
  cTheta_ge_neg_one_of_paperTheta_le l logQ dmod dFpd fFpd eStar etaPrm
    hq hincl habs (by rw [hH] at hThetaH; exact hThetaH) hA hB

#print axioms cTheta_ge_neg_one_of_H_readout

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual
