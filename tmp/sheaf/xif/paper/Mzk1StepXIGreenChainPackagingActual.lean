import tmp.sheaf.xif.paper.Mzk1AcceptanceEvidenceBundleActual
import tmp.sheaf.xif.paper.Mzk1StepXIAcceptanceEvidenceManifestActual
import tmp.sheaf.xif.paper.Mzk1StepXIFinalAcceptanceWrapperActual
import tmp.sheaf.xif.paper.Mzk1StepXIStrictnessActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final green-chain packaging

Re-exports the green evidence bundle, stepxi evidence manifest, acceptance wrapper,
and strictness lemmas as one packaging module. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessActual

theorem stepxi_packaging_oneDim {a b : Real} (ha : 0 < a) (h : a < b) :
    ENNReal.ofReal a < ENNReal.ofReal b :=
  oneDim_ennreal_strict ha h

theorem stepxi_packaging_product {α : Type*} [Fintype α]
    (f g : α → NNReal) (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i :=
  product_strict f g hle hlt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenChainPackagingActual

end
