import tmp.sheaf.xif.paper.Mzk1StepXIGreenChainPackagingV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIProductStrictnessConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi green-chain packaging consumer

Consumes the green PackagingV2 and ProductStrictnessConsumer. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIProductStrictnessConsumerActual

theorem packaging_consumer_product {α : Type*} [Fintype α]
    (f g : α → Real) (hf : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i :=
  stepxi_packaging_product f g hf hle hlt

theorem packaging_consumer_oneDim {a b : Real} (ha : 0 < a) (h : a < b) :
    ENNReal.ofReal a < ENNReal.ofReal b :=
  stepxi_packaging_oneDim ha h

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingConsumerActual

end
