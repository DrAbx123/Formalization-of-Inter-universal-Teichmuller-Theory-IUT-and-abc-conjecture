import tmp.sheaf.xif.paper.Mzk1StepXICarrierBadInvScaleConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi carrier bad-inverse law, real part

Real-valued part of the carrier bad-inverse scaling law. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleLawPartAActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleConsumerActual

theorem carrier_real_product_law {ι : Type*} [Fintype ι]
    (f : ι → Real) {c : Real} (hc : c ≠ 0) :
    (∏ i, c⁻¹ * f i) = c⁻¹ ^ (Fintype.card ι) * ∏ i, f i :=
  carrier_badInvScale_prod_law f hc

end LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleLawPartAActual

end
