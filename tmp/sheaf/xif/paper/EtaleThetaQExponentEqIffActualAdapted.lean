import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentEqIffActualAdapted

theorem thetaQExponent_eq_iff (a b : Int) :
    thetaQExponent a = thetaQExponent b ↔ a = b ∨ a + b = -1 := by
  constructor
  · intro h
    have hfac : ((a : Rat) - (b : Rat)) * ((a : Rat) + (b : Rat) + 1) = 0 := by
      unfold thetaQExponent at h
      nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left; exact_mod_cast (sub_eq_zero.mp h1)
    · right; omega
  · rintro (rfl | h)
    · rfl
    · unfold thetaQExponent
      rw [show (b : Rat) = -(a : Rat) - 1 by omega]
      ring

#check thetaQExponent_eq_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentEqIffActualAdapted
