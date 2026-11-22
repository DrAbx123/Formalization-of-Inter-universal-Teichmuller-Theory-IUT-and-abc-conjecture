import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi bad inverse scaling product law V2

Real-valued inverse scaling product law, independent of the hull owner file. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIBadInvScaleProductLawV2Actual

def badInvScale (c : Real) : Real := c⁻¹

theorem badInvScale_mul_cancel {c : Real} (hc : c ≠ 0) :
    badInvScale c * c = 1 := by
  unfold badInvScale
  field_simp

theorem prod_badInvScale_law {ι : Type*} [Fintype ι] (f : ι → Real) {c : Real}
    (hc : c ≠ 0) :
    (∏ i, badInvScale c * f i) = (badInvScale c) ^ (Fintype.card ι) * ∏ i, f i := by
  calc ∏ i, badInvScale c * f i = (∏ i, (badInvScale c : Real)) * ∏ i, f i := Finset.prod_mul_distrib
    _ = (badInvScale c) ^ (Fintype.card ι) * ∏ i, f i := by
        rw [Finset.prod_const, Finset.card_univ]

end LeanFormal.IUT.XiFPaper.Mzk1StepXIBadInvScaleProductLawV2Actual

end
