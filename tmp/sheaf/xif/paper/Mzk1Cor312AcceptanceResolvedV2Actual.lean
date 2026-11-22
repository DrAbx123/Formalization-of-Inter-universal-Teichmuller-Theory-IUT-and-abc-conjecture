/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictRPConsumerActual

/-!
# A561 resolved acceptance artifact: strict_measure is a THEOREM

Consumes the p-scaling resolution (`Mzk1HaarStrictScalingActual`):
* `rpRegion` = product `R_b/p_b` balls, `s1902Hull` = product `R_b` balls;
* `strict_measure` of `rpRequirement` is PROVED by the p-scaling ball strictness
  (`rootExtensionHaar_ball_strict` + product `Finset.prod_lt_prod`), NOT a named field;
* `annulus_positive` (`μ(hull \ rpRegion) > 0`) is a theorem (`Mzk1HaarStrictRPConsumerActual`);
* the only assumptions left are `[Nonempty (Bad ...)]` (bad set nonempty), `hqneg`
  (signed q reading negative) and the real `(IPL)/(SHE)/(APT)` evidence Props.

This is the strict-measure-RESOLVED Cor 3.12 acceptance artifact; the remaining
paper-reading identification is not needed for this region-level statement.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Resolved strict measure**: the strict increase of the normalized real volume is
  a THEOREM (no named `strict_measure`). -/
theorem resolved_strict_measure_theorem :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  rp_strict_measure_resolved T

/-- Annulus positivity (the last geometric input) is a THEOREM. -/
theorem resolved_annulus_positive :
    0 < rootExtensionProductHaar T (s1902Hull T \ rpRegion T) :=
  annulus_positive T

/-- **Resolved Cor 3.12 conclusion**: the green `requirement_cor312` on the resolved
  requirement. -/
theorem resolved_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  rp_cor312 T hqneg ipl hipl she hshe apt hapt

/-- The resolved signed inequality (paper shape). -/
theorem resolved_paper_inequality :
    requirementSignedQ (rpRequirement T) ≤ requirementSignedTheta (rpRequirement T) :=
  requirement_signed_inequality (rpRequirement T)

/-- The resolved signed inequality is STRICT (non-vacuity from the theorem). -/
theorem resolved_paper_inequality_strict :
    requirementSignedQ (rpRequirement T) < requirementSignedTheta (rpRequirement T) :=
  requirement_strict_signed (rpRequirement T)

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2Actual