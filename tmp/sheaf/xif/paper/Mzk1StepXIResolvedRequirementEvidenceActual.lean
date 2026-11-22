import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi resolved requirement evidence

Evidence that the resolved requirement's q_pos/strict_measure come from the
positive half-ball measure and the strict Haar annulus input. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementEvidenceActual

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

theorem stepxi_resolved_q_pos (D : PositiveQRegionHaarStrict T) :
    0 < qNormalizedVolume T (qRegion T) :=
  resolved_q_pos T D

theorem stepxi_resolved_strict_measure (D : PositiveQRegionHaarStrict T) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  resolved_strict_measure T D

theorem stepxi_resolved_acceptance (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  resolved_cor312 T D hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementEvidenceActual

end
