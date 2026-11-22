import tmp.sheaf.xif.paper.Mzk1StepXIStrictnessV3Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi product strictness consumer

Re-exports the 1D and product strictness lemmas from the green StrictnessV3. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIProductStrictnessConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessV3Actual

theorem product_strict_consumer {α : Type*} [Fintype α]
    (f g : α → Real) (hf : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) :
    (∏ i, f i) < ∏ i, g i :=
  product_strict f g hf hle hlt

theorem oneDim_strict_consumer {a b : Real} (ha : 0 < a) (h : a < b) :
    ENNReal.ofReal a < ENNReal.ofReal b :=
  oneDim_ennreal_strict ha h

end LeanFormal.IUT.XiFPaper.Mzk1StepXIProductStrictnessConsumerActual

end
