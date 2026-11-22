import tmp.sheaf.xif.paper.Mzk1StepXICanonicalInterfaceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi hqneg clean gate (stepxi-owned name)

The hqneg model files are hull/mainline-owned.  This file only records the clean
gate of the stepxi canonical interface; hqneg remains an explicit hypothesis. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegGateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXICanonicalInterfaceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_hqneg_gate (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  canonical_resolved_acceptance T D hqneg ipl hipl she hshe apt hapt

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICanonicalInterfaceActual.canonical_resolved_acceptance
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICanonicalInterfaceActual.canonical_twoGaps_ABC

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegGateActual

end
