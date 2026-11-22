import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreQExponentInvolutionActual

theorem thetaQExponent_involution (n : Int) :
    thetaQExponent (-(-n - 1) - 1) = thetaQExponent n := by
  rw [show (-(-n - 1) - 1 : Int) = n by ring]

theorem thetaQExponent_pair (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := thetaQExponent_neg_succ n

theorem thetaQExponent_pair_twice (n : Int) :
    thetaQExponent (-(-n - 1) - 1) = thetaQExponent n ∧
      thetaQExponent (-n - 1) = thetaQExponent n :=
  ⟨thetaQExponent_involution n, thetaQExponent_pair n⟩

#check thetaQExponent_involution
#check thetaQExponent_pair
#check thetaQExponent_pair_twice

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreQExponentInvolutionActual
