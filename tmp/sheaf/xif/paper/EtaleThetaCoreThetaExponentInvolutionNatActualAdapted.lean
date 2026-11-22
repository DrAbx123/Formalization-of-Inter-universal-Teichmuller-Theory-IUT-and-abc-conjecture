import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentInvolutionNatActualAdapted

theorem thetaExponent_neg_nat (n : Nat) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-(n : Int) - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (n : Int) := by
  rw [show (-(n : Int) - 1 : Int) = -((n : Int) + 1) by ring]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  push_cast
  ring

theorem thetaExponent_neg_nat_succ (n : Nat) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-(n : Int) - 2) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent ((n + 1 : Nat) : Int) := by
  have h' : (-(n : Int) - 2 : Int) = -(((n + 1 : Nat) : Int) + 1) by
    push_cast; ring
  rw [h']
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  push_cast
  ring

#check thetaExponent_neg_nat
#check thetaExponent_neg_nat_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentInvolutionNatActualAdapted
