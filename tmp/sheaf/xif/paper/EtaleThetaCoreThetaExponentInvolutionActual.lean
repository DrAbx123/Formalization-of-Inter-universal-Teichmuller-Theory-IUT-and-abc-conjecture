import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentInvolutionActual

theorem thetaExponent_pair (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

theorem thetaExponent_involution (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-(-n - 1) - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n := by
  rw [show (-(-n - 1) - 1 : Int) = n by ring]

#check thetaExponent_pair
#check thetaExponent_involution

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentInvolutionActual
