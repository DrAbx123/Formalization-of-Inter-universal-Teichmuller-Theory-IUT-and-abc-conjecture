import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreQExponentInvolutionNatActual

theorem thetaQExponent_neg_nat (n : Nat) :
    thetaQExponent (-(n : Int) - 1) = thetaQExponent (n : Int) := by
  rw [thetaQExponent_neg_succ]

theorem thetaQExponent_neg_nat_succ (n : Nat) :
    thetaQExponent (-(n : Int) - 2) = thetaQExponent ((n + 1 : Nat) : Int) := by
  have h := thetaQExponent_neg_succ ((n + 1 : Nat) : Int)
  have h' : -((n + 1 : Nat) : Int) - 1 = -(n : Int) - 2 := by
    push_cast; ring
  rw [h'] at h
  exact h

#check thetaQExponent_neg_nat
#check thetaQExponent_neg_nat_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreQExponentInvolutionNatActual
