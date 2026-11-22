import tmp.sheaf.xif.paper.Mzk1StepXIBadPartLogNormalizedActual
import tmp.sheaf.xif.paper.Mzk1StepXIBadPartProductLawActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi badPart arithmetic wrap-up

Combined badPart/log/normalized arithmetic statement. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartWrapUpActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartLogNormalizedActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartProductLawActual

theorem badPart_wrapup {c : Real} (hc : c ≠ 0) :
    badPart c * c = 1 ∧
      (∀ {ι : Type*} [Fintype ι] (f : ι → Real),
        (∏ i, badPart c * f i) = (badPart c) ^ (Fintype.card ι) * ∏ i, f i) :=
  ⟨badPart_mul_cancel hc, fun f => prod_badPart_law f hc⟩

theorem badPart_log_wrapup (c : Real) :
    normalizedScale c = c / logScale c := normalizedScale_eq c

end LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartWrapUpActual

end
