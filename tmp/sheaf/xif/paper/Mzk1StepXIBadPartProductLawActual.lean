import tmp.sheaf.xif.paper.Mzk1StepXIBadPartLogNormalizedActual
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi bad part product law

Product law for `badPart c = c⁻¹`, the inverse scaling factor. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartProductLawActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartLogNormalizedActual

theorem prod_badPart_law {ι : Type*} [Fintype ι] (f : ι → Real) {c : Real}
    (hc : c ≠ 0) :
    (∏ i, badPart c * f i) = (badPart c) ^ (Fintype.card ι) * ∏ i, f i := by
  calc ∏ i, badPart c * f i = (∏ i, (badPart c : Real)) * ∏ i, f i := Finset.prod_mul_distrib
    _ = (badPart c) ^ (Fintype.card ι) * ∏ i, f i := by
        rw [Finset.prod_const, Finset.card_univ]

theorem prod_badPart_law_apply {ι : Type*} [Fintype ι] (f : ι → Real)
    {c : Real} (hc : c ≠ 0) :
    (∏ i, c⁻¹ * f i) = c⁻¹ ^ (Fintype.card ι) * ∏ i, f i := by
  simpa [badPart] using prod_badPart_law f hc

end LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartProductLawActual

end
