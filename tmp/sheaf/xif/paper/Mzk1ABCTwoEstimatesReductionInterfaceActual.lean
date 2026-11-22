/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesNumericEvidenceActual
import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual

/-!
# A598 CANONICAL two-estimates reduction INTERFACE (mainline)

Thin interface for the unique remaining ABC gap `ABCTwoEstimates`:
* `two_estimates_to_abc` / `two_estimates_to_heightBound`;
* `two_estimates_gap_equiv`: the gap is exactly one datum;
* `two_estimates_certificate`: the final conditional certificate consumption;
* `bridge_certificate`: the bridge-interface route.

No new mathematics; conditional only (ABC gate NOT passed). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EstimateGapsActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericEvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual

/-- The two estimates imply the ABC conjecture. -/
theorem two_estimates_to_abc (E : ABCTwoEstimates) : ABCConjecture :=
  abc_of_twoEstimates E

/-- The two estimates imply the ABC-form additive height bound. -/
theorem two_estimates_to_heightBound (E : ABCTwoEstimates) :
    ABCFormAdditiveHeightBound :=
  heightBound_of_twoEstimates E

/-- The gap record is exactly one datum. -/
theorem two_estimates_gap_equiv :
    Nonempty ABCTwoEstimates ↔ Nonempty ABCStage5Gaps :=
  nonempty_twoEstimates_iff_gaps

/-- Final certificate consumption: the two estimates give `ABCConjecture` through
  the GREEN certificate. -/
theorem two_estimates_certificate (E : ABCTwoEstimates) : ABCConjecture :=
  final_abc_of_twoEstimates E

/-- Bridge route: a nonempty bridge interface gives `ABCConjecture`. -/
theorem bridge_certificate (h : Nonempty Cor312ToABCBridgeInterface) : ABCConjecture :=
  final_abc_of_bridge h

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionInterfaceActual

end
