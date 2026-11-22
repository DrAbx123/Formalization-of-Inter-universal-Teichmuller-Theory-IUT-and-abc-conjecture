import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi resolved requirement acceptance

Consumer of the green resolved acceptance (`ResolvedStrictAcceptanceV3`). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_resolved_acceptance (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  resolved_cor312 T D hqneg ipl hipl she hshe apt hapt

theorem stepxi_resolved_paper (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) <=
      requirementSignedTheta (resolvedRequirement T D) :=
  resolved_paper_inequality T D

end LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementAcceptanceActual

end
