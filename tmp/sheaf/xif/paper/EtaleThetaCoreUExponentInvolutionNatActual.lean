import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentInvolutionNatActual

theorem thetaUExponent_neg_nat (n : Nat) :
    thetaUExponent (-(n : Int) - 1) = -thetaUExponent (n : Int) := by
  rw [thetaUExponent_neg_succ]

theorem thetaUExponent_neg_nat_succ (n : Nat) :
    thetaUExponent (-(n : Int) - 2) = -thetaUExponent ((n + 1 : Nat) : Int) := by
  have h := thetaUExponent_neg_succ ((n + 1 : Nat) : Int)
  have h' : -((n + 1 : Nat) : Int) - 1 = -(n : Int) - 2 := by
    push_cast; ring
  rw [h'] at h
  exact h

#check thetaUExponent_neg_nat
#check thetaUExponent_neg_nat_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentInvolutionNatActual
