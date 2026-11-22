/- R5: scale invariance of the boundary distance `rhoDist`, giving a well-defined function
`rhoP1` on the projective line `P1(L)` (pairs modulo scaling by nonzero constants).
REUSE: `Mzk1G1GKRhoDistanceActual.rhoDist` (this lane). DEDUP: scale invariance was not
formalized. -/
import tmp.sheaf.xif.paper.Mzk1G1GKRhoZeroActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoSmulActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoDistanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoZeroActual

variable {L : Type*} [NormedField L]

/-- **Scale invariance**: `rhoDist` is invariant under multiplication of both entries by a
nonzero constant — it is a function on `P1(L)`. -/
theorem rhoDist_smul (c : L) (hc : c ≠ 0) (a b : L) :
    rhoDist (c * a) (c * b) = rhoDist a b := by
  have hr : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have e1 : ‖c * a‖ = ‖c‖ * ‖a‖ := norm_mul c a
  have e2 : ‖c * b‖ = ‖c‖ * ‖b‖ := norm_mul c b
  have e3 : ‖c * a - c * b‖ = ‖c‖ * ‖a - b‖ := by
    rw [← mul_sub, norm_mul]
  unfold rhoDist
  rw [e1, e2, e3]
  have hmin1 : min (‖c‖ * ‖a‖) (‖c‖ * ‖b‖) = ‖c‖ * min ‖a‖ ‖b‖ := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hr.le)]
    · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hr.le)]
  have hmin2 : min (min (‖c‖ * ‖a‖) (‖c‖ * ‖b‖)) (‖c‖ * ‖a - b‖)
      = ‖c‖ * min (min ‖a‖ ‖b‖) ‖a - b‖ := by
    rw [hmin1]
    rcases le_total (min ‖a‖ ‖b‖) (‖a - b‖) with h | h
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hr.le)]
    · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hr.le)]
  have hmax : max (‖c‖ * ‖a‖) (‖c‖ * ‖b‖) = ‖c‖ * max ‖a‖ ‖b‖ := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hr.le)]
    · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hr.le)]
  rw [hmin2, hmax]
  exact mul_div_mul_left _ _ hr.ne'

end LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoSmulActual
