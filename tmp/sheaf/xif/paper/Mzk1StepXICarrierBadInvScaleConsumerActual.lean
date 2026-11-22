import tmp.sheaf.xif.paper.Mzk1StepXIBadInvScaleProductLawV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIHullProductScalingLawActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi carrier bad-inverse scaling consumer

Consumer connecting the bad inverse scaling factor to the hull product scaling law,
in the form required by the carrier product. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIBadInvScaleProductLawV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHullProductScalingLawActual

theorem carrier_badInvScale_prod_law {ι : Type*} [Fintype ι]
    (f : ι → Real) {c : Real} (hc : c ≠ 0) :
    (∏ i, badInvScale c * f i) =
      (badInvScale c) ^ (Fintype.card ι) * ∏ i, f i :=
  prod_badInvScale_law f hc

theorem carrier_badInvScale_ennreal_prod_law {ι : Type*} [Fintype ι]
    (g : ι → ENNReal) (c : ENNReal) :
    (∏ i, c * g i) = c ^ (Fintype.card ι) * ∏ i, g i :=
  prod_scaling_law_one g c

end LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleConsumerActual

end
