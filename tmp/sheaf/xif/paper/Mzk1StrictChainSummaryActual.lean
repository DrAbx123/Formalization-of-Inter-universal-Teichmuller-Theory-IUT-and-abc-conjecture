/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementResolvedActual

/-!
# A596 strict chain SUMMARY (mainline lane)

The strict-measure chain, all PROVED in the mainline lane:
* 1D p-scaling strict ball measure (`rootExtensionHaar_ball_strict`);
* product strictness of the `R/p` region vs the hull (`rpRegion_measure_lt_hull`);
* real strict measure `rp_strict_measure_resolved` (requirement's `strict_measure`);
* Cor 3.12 at requirement level (`resolvedCor312`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- 1D strict ball measure (quotient radius `R/p` vs `R`). -/
theorem strict_chain_1D (b : Bad (nativePlaceSelection T)) (R : ℝ) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : ℝ))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
  rootExtensionHaar_ball_strict T b R hR

/-- Product strictness: the `R/p` region is strictly smaller than the hull. -/
theorem strict_chain_product :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  rpRegion_measure_lt_hull T

/-- Real strict measure: the requirement's `strict_measure` is a THEOREM. -/
theorem strict_chain_measure_real :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  rp_strict_measure_resolved T

/-- Cor 3.12 at requirement level, from the resolved strict chain. -/
theorem strict_chain_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  rp_cor312 T hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryActual

end
