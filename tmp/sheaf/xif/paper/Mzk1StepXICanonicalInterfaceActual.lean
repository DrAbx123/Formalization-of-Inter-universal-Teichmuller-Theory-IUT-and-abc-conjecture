import tmp.sheaf.xif.paper.Mzk1StepXIResolvedRequirementAcceptanceActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi canonical interface (thin re-export)

Re-exports the canonical 3.12 acceptance and ABC two-gap interfaces from the
green resolved/two-gap files, without changing them. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICanonicalInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIResolvedRequirementAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem canonical_resolved_acceptance (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  stepxi_resolved_acceptance T D hqneg ipl hipl she hshe apt hapt

theorem canonical_twoGaps_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXICanonicalInterfaceActual

end
