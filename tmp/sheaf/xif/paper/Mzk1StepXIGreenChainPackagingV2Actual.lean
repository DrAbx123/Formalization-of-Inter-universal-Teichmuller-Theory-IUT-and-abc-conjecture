import tmp.sheaf.xif.paper.Mzk1AcceptanceEvidenceBundleActual
import tmp.sheaf.xif.paper.Mzk1StepXIAcceptanceEvidenceManifestActual
import tmp.sheaf.xif.paper.Mzk1StepXIFinalAcceptanceWrapperV3Actual
import tmp.sheaf.xif.paper.Mzk1StepXIStrictnessV3Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final green-chain packaging V2

Uses the green StrictnessV3 and WrapperV3 dependencies. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessV3Actual

theorem stepxi_packaging_oneDim {a b : Real} (ha : 0 < a) (h : a < b) :
    ENNReal.ofReal a < ENNReal.ofReal b :=
  oneDim_ennreal_strict ha h

theorem stepxi_packaging_product {α : Type*} [Fintype α]
    (f g : α → Real) (hf : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i :=
  product_strict f g hf hle hlt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingV2Actual

end
