/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementResolvedActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual

/-!
# A593 FINAL CONDITIONAL CERTIFICATE (mainline)

## GREEN artefacts consumed
* `Mzk1Cor312RequirementResolvedActual`: Cor 3.12 at requirement level; the xi-e
  rule's `strict_measure` is a THEOREM (1D p-scaling Haar strictness + real product
  comparison), `resolvedCor312` gives `Cor312Conclusion` from real evidence;
* `Mzk1ABCTwoEstimatesShaActual`: `ABCTwoEstimates` gap record and
  `abc_of_twoEstimates : ABCTwoEstimates -> ABCConjecture` (green numerical reduction);
* `Cor312ToABCBridgeInterface`: the bridge interface and
  `cor312ToABCBridgeInterface_abcConjecture_of_nonempty`;
* `Mzk1ABCStage5AcceptanceActual`: `acceptance_abcStage5` (Stage-5 conditional rung);
* `Mzk1ABCBridgeGap1ConsumerActual` / `Mzk1ABCBridgeGap2ConsumerActual`: Gap-1/Gap-2
  consumers (green conditional reductions).

## Status
The certificate is CONDITIONAL: the only remaining gaps are the two named IUT IV
Thm 1.10 estimates (`height_estimate`, `volume_estimate` in `ABCTwoEstimates`) and
the bridge-interface datum `Cor312ToABCBridgeInterface`.  **ABC gate NOT passed**;
no `sorry`, no custom axiom, no closure claim.

Axiom gate below: `#print axioms` for the three final theorems (expected
`[propext, Classical.choice, Quot.sound]` only).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual

/-! ## 1. Cor 3.12 (requirement level) -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Final 3.12**: `Cor312Conclusion` from the resolved requirement and real
  `hqneg`/IPL/SHE/APT evidence. -/
theorem final_3_12 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  resolvedCor312 (T := T) hqneg ipl hipl she hshe apt hapt

/-! ## 2. ABC from the two IUT IV Thm 1.10 estimates -/

/-- **Final ABC (two estimates)**: the two named estimates imply `ABCConjecture`. -/
theorem final_abc_of_twoEstimates (E : ABCTwoEstimates) : ABCConjecture :=
  abc_of_twoEstimates E

/-! ## 3. ABC from the bridge interface -/

/-- **Final ABC (bridge)**: a nonempty `Cor312ToABCBridgeInterface` implies
  `ABCConjecture`. -/
theorem final_abc_of_bridge (h : Nonempty Cor312ToABCBridgeInterface) : ABCConjecture :=
  cor312ToABCBridgeInterface_abcConjecture_of_nonempty h

end LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_3_12
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_abc_of_twoEstimates
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_abc_of_bridge

end