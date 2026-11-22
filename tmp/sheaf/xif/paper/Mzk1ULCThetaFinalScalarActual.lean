/- Final scalar: R1.1 lower bound -M <= paperTheta and R2 upper
   paperTheta <= CThetaPaper * paperQAbsLog combine to -M <= CThetaPaper * paperQAbsLog,
   and (with the q-ray data) to the C4 scalar -1 <= CTheta.
   Both scalar bounds are explicit hypotheses; no fake equality, no new H variable. -/
import tmp.sheaf.xif.paper.Mzk1ULCThetaR2InstantiationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalScalarActual

open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaR2InstantiationActual

/-- Scalar transitivity: R1.1 lower bound and R2 upper bound give
    -M <= CThetaPaper * paperQAbsLog. -/
theorem neg_M_le_CThetaPaper_mul_A
    (M : Real) (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {paperTheta : Real}
    (hR1 : -M ≤ paperTheta)
    (hR2 : paperTheta ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ) :
    -M ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ :=
  le_trans hR1 hR2

/-- Final scalar assembly: both bounds plus q-ray data give
    (-M <= CThetaPaper*A) and (-1 <= CTheta). -/
theorem final_scalar_assembly
    (M : Real) (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {paperTheta qParameter : Real}
    (hR1 : -M ≤ paperTheta)
    (hR2 : paperTheta ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ paperTheta)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    (-M ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ) ∧
    (-1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm) := by
  refine ⟨neg_M_le_CThetaPaper_mul_A M l logQ dmod dFpd fFpd eStar etaPrm hR1 hR2, ?_⟩
  exact cTheta_ge_neg_one_of_paperTheta_le_CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm
    hR2 hq hincl habs hA hB

#print axioms neg_M_le_CThetaPaper_mul_A
#print axioms final_scalar_assembly

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalScalarActual