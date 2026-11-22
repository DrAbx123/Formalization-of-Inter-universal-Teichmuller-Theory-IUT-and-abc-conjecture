import tmp.sheaf.xif.paper.Mzk1StepXIResolvedRequirementEvidenceActual
import tmp.sheaf.xif.paper.Mzk1StepXIResolvedRequirementAcceptanceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi strict chain summary

Thin re-export of the resolved strict chain: positive q-region, strict gain, strict
paper inequality, and Cor312Conclusion. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictChainSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementEvidenceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_strict_chain_summary (D : PositiveQRegionHaarStrict T) :
    0 < qNormalizedVolume T (qRegion T) ∧
      qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) ∧
      requirementSignedQ (resolvedRequirement T D) <
        requirementSignedTheta (resolvedRequirement T D) :=
  ⟨stepxi_resolved_q_pos T D, stepxi_resolved_strict_measure T D,
    resolved_paper_inequality_strict T D⟩

theorem stepxi_strict_chain_cor312 (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  stepxi_resolved_acceptance T D hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictChainSummaryActual

end
