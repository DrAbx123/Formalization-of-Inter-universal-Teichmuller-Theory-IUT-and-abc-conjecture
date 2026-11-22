/- Exact final C4 theorem consuming R1.1 lower bound (-Mpaper_v2 <= paperTheta) and
   R2 upper (paperTheta <= CThetaPaper * paperQAbsLog), plus the q-ray data.
   Instantiation of Mzk1ULCThetaFinalScalarActual.final_scalar_assembly at the actual
   M_paper_v2 from the R1.1 consumer. No fake equality. -/
import tmp.sheaf.xif.paper.Mzk1ULCThetaR2InstantiationActual
import tmp.sheaf.xif.paper.Mzk1ULR0FullFiberActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalC4Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4ComposeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaC4HWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULCThetaR2InstantiationActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Final C4 theorem: R1.1 (-Mpaper_v2 <= paperTheta) + R2 (paperTheta <= CThetaPaper*A)
    + q-ray data give (-Mpaper_v2 <= CThetaPaper*A) and (-1 <= CTheta). -/
theorem final_C4_of_R1_R2
    (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {paperTheta qParameter : Real}
    (hR1 : - M_paper_v2 (l := l) T ≤ paperTheta)
    (hR2 : paperTheta ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ)
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ paperTheta)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    (- M_paper_v2 (l := l) T ≤
        CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog l logQ) ∧
      (-1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm) := by
  refine ⟨le_trans hR1 hR2, ?_⟩
  exact cTheta_ge_neg_one_of_paperTheta_le_CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm
    hR2 hq hincl habs hA hB

#print axioms final_C4_of_R1_R2

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFinalC4Actual