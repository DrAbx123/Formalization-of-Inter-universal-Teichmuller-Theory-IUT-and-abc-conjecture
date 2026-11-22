import tmp.sheaf.xif.paper.Mzk1Cor312NumericalContentActual

/-! # Mzk1CThetaConsumerIndependentActual — independent C_Theta >= -1 consumer (numeric)

A545 consumer module (no new mathematics): from the Unit X numeric pilot values
(mu_q = -L/2, mu_theta = -L/6), computes the calibrated constant
C = mu_theta / (-mu_q) = -1/3 and checks `C >= -1`, independently of the pending
Kummer/FinalStatement chain.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaConsumerIndependentActual

open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual

/-- The calibrated constant of the numeric instance: C = mu_theta / (-mu_q). -/
noncomputable def numericCTheta (L : Real) : Real := muTheta L / (-muQ L)

/-- Numeric C_Theta is exactly `-1/3` for L > 0. -/
theorem numericCTheta_eq (L : Real) (hL : 0 < L) : numericCTheta L = -(1 / 3) := by
  unfold numericCTheta muTheta muQ
  have hL0 : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-- The calibrated constant satisfies the paper bound `C >= -1`. -/
theorem numericCTheta_ge_neg_one (L : Real) (hL : 0 < L) : -1 <= numericCTheta L := by
  rw [numericCTheta_eq L hL]
  norm_num

/-- The calibration identity: mu_theta = C * (-mu_q). -/
theorem numericCTheta_calibrated (L : Real) (hL : 0 < L) :
    muTheta L = numericCTheta L * (-muQ L) := by
  unfold numericCTheta muTheta muQ
  have hL0 : L ≠ 0 := ne_of_gt hL
  field_simp

#check numericCTheta
#check numericCTheta_eq
#check numericCTheta_ge_neg_one
#check numericCTheta_calibrated

end LeanFormal.IUT.XiFPaper.Mzk1CThetaConsumerIndependentActual
end
