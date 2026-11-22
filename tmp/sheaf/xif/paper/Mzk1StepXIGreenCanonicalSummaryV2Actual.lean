import tmp.sheaf.xif.paper.Mzk1StepXIStrictChainSummaryActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXIFinalCertificateV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi canonical green summary

Read-only summary of the green stepxi canonical files (strict chain, two-gap
reduction, final certificate). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenCanonicalSummaryV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictChainSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementEvidenceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_green_canonical_summary (D : PositiveQRegionHaarStrict T) :
    0 < qNormalizedVolume T (qRegion T) ∧
      qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) := 
  ⟨stepxi_resolved_q_pos T D, stepxi_resolved_strict_measure T D⟩

theorem stepxi_green_canonical_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoEstimates_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenCanonicalSummaryV2Actual

end
