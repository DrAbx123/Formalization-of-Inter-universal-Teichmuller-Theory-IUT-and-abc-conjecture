import tmp.sheaf.xif.paper.Mzk1StepXICarrierBadInvScaleConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi carrier bad-inverse law, ENNReal part

ENNReal-valued part of the carrier bad-inverse scaling law. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleLawPartBActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleConsumerActual

theorem carrier_ennreal_product_law {ι : Type*} [Fintype ι]
    (g : ι → ENNReal) (c : ENNReal) :
    (∏ i, c * g i) = c ^ (Fintype.card ι) * ∏ i, g i :=
  carrier_badInvScale_ennreal_prod_law g c

end LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierBadInvScaleLawPartBActual

end
