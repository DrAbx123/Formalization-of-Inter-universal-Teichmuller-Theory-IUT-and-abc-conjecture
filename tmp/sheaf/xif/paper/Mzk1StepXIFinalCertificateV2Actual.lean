import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import tmp.sheaf.xif.paper.Mzk1StepXIResolvedRequirementAcceptanceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final certificate

Combines the two-gap ABC formalization with the resolved 3.12 acceptance:
`Cor312Conclusion` and `ABCConjecture` are both fields of one certificate. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalCertificateV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure StepXIFinalCertificateInput where
  gaps : StepXIABCTwoGaps
  D : PositiveQRegionHaarStrict T
  hqneg : requirementSignedQ (resolvedRequirement T D) < 0
  ipl : Prop
  hipl : ipl
  she : Prop
  hshe : she
  apt : Prop
  hapt : apt

def stepxiFinalCertificateCor312 (I : StepXIFinalCertificateInput T) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T I.D) I.hqneg
        I.ipl I.hipl I.she I.hshe I.apt I.hapt) :=
  stepxi_resolved_acceptance T I.D I.hqneg I.ipl I.hipl I.she I.hshe I.apt I.hapt

theorem stepxi_final_certificate (I : StepXIFinalCertificateInput T) :
    Cor312Conclusion
        (requirementContract (resolvedRequirement T I.D) I.hqneg
          I.ipl I.hipl I.she I.hshe I.apt I.hapt) ∧
      ABCConjecture :=
  ⟨stepxiFinalCertificateCor312 T I, stepxi_twoGaps_ABC I.gaps⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalCertificateV2Actual

end
