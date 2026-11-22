import tmp.sheaf.xif.paper.S679DirectScalarComparisonActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S693DirectComparisonCounterexampleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S679DirectScalarComparisonActual

/-- The actual prime label l = 29. -/
def l29 : PrimeGeFive where
  value := 29
  prime := by norm_num
  ge_five := by norm_num

theorem l29_value : l29.value = 29 := rfl

theorem card_SignedLabel_29 :
    Fintype.card (SignedLabel l29.value) = 29 := by
  rw [SignedLabel.card_signedLabel]
  rfl

theorem sum_fl_29 :
    (∑ x : Fl l29.value,
      (gaussExponent ((SignedLabel.equiv l29).symm x).1).toNat) = 2030 := by
  native_decide

theorem gaussExponentSumNat_29 :
    (∑ j : SignedLabel l29.value, (gaussExponent j.1).toNat) = 2030 := by
  rw [Fintype.sum_equiv (SignedLabel.equiv l29)
    (fun j : SignedLabel l29.value => (gaussExponent j.1).toNat)
    (fun x : Fl l29.value =>
      (gaussExponent ((SignedLabel.equiv l29).symm x).1).toNat)
    (by intro j; rw [Equiv.symm_apply_apply])]
  exact sum_fl_29

theorem gaussExponentSum_29 :
    (∑ j : SignedLabel l29.value, ((gaussExponent j.1).toNat : Real)) = 2030 := by
  exact_mod_cast gaussExponentSumNat_29

theorem rootThetaAverageCoefficient_l29 :
    rootThetaAverageCoefficient (l := l29) = (2030 : Real) / (2 * 29 * 29) := by
  unfold rootThetaAverageCoefficient
  rw [gaussExponentSum_29, card_SignedLabel_29]
  norm_num [l29]

theorem rootThetaAverageCoefficient_l29_gt_one :
    (1 : Real) < rootThetaAverageCoefficient (l := l29) := by
  rw [rootThetaAverageCoefficient_l29]
  norm_num

/-- Exact counterexample: at l = 29 the direct scalar comparison condition fails. -/
theorem not_directScalarComparisonCondition_l29 :
    ¬ DirectScalarComparisonCondition (l := l29) := by
  unfold DirectScalarComparisonCondition
  rw [rootThetaAverageCoefficient_l29]
  norm_num

end LeanFormal.IUT.XiFPaper.S693DirectComparisonCounterexampleActual

end
