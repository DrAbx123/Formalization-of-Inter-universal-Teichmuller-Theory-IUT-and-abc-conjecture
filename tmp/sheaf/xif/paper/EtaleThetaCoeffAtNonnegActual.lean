import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtNonnegActual

theorem thetaQExponent_nonneg {n : Int} (h : 0 <= n) :
    0 <= thetaQExponent n := by
  unfold thetaQExponent
  have hn : (0 : Rat) <= (n : Rat) := by exact_mod_cast h
  have hn1 : (0 : Rat) <= (n : Rat) + 1 := by positivity
  positivity

theorem thetaQExponent_pos {n : Int} (h : 0 < n) :
    0 < thetaQExponent n := by
  unfold thetaQExponent
  have hn : (0 : Rat) < (n : Rat) := by exact_mod_cast h
  have hn1 : (0 : Rat) < (n : Rat) + 1 := by linarith
  positivity

theorem thetaUExponent_pos {n : Int} (h : 0 <= n) :
    0 < thetaUExponent n := by
  unfold thetaUExponent
  omega

#check thetaQExponent_nonneg
#check thetaQExponent_pos
#check thetaUExponent_pos

end LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtNonnegActual
