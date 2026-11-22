import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Cor312NumericalContentActual — numerical content of Cor 3.12 (Unit X)

Lean transcription of the exact real arithmetic of the mined independent verification
script 24_corollary_3_12_numerical (laichunwing, IUT-Verification, Unit X) for 11a1:
with L = log q > 0, the q-pilot log-volume is mu_q = -(1/2) L, the Theta-pilot
log-volume is mu_theta = -(1/6) L, the Cor 3.12 comparison mu_theta >= mu_q holds, and
the gap is (1/3) L > 0.  Pure real arithmetic; no structural claim.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual

/-- The q-pilot log-volume at the numerical instance: mu_q = -(1/2) L. -/
noncomputable def muQ (L : Real) : Real := -(1 / 2) * L

/-- The Theta-pilot log-volume at the numerical instance: mu_theta = -(1/6) L. -/
noncomputable def muTheta (L : Real) : Real := -(1 / 6) * L

/-- Cor 3.12 comparison at the numerical instance: mu_theta >= mu_q. -/
theorem cor312_numerical_holds (L : Real) (hL : 0 < L) : muQ L <= muTheta L := by
  unfold muQ muTheta
  linarith

/-- The gap between the pilots: mu_theta - mu_q = (1/3) L. -/
theorem cor312_gap_eq (L : Real) : muTheta L - muQ L = (1 / 3) * L := by
  unfold muQ muTheta
  ring

/-- The gap is positive. -/
theorem cor312_gap_pos (L : Real) (hL : 0 < L) : 0 < muTheta L - muQ L := by
  rw [cor312_gap_eq]
  linarith

/-- The calibrated constant C_theta = mu_theta / L = -1/6. -/
noncomputable def cTheta : Real := -(1 / 6)

/-- Cor 3.12 constant conclusion at the numerical instance: C_theta >= -1. -/
theorem cor312_cTheta_ge_neg_one : -1 <= cTheta := by
  unfold cTheta
  norm_num

/-- Relation between the calibrated constant and the pilot volumes. -/
theorem cTheta_mul_eq (L : Real) : cTheta * L = muTheta L := by
  unfold cTheta muTheta
  ring

#check muQ
#check muTheta
#check cor312_numerical_holds
#check cor312_gap_eq
#check cor312_gap_pos
#check cor312_cTheta_ge_neg_one

end LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual
end
