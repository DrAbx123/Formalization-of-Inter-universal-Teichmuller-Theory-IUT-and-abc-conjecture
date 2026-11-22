import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionNatActual

universe u

theorem thetaCoeffAt_neg_nat (K : Type u) [Field K] (n : Nat) :
    thetaCoeffAt K (-(n : Int) - 1) = thetaCoeffAt K (n : Int) := by
  simpa using thetaCoeffAt_pair K (n : Int)

theorem thetaCoeffAt_neg_nat_succ (K : Type u) [Field K] (n : Nat) :
    thetaCoeffAt K (-(n : Int) - 2) = thetaCoeffAt K ((n + 1 : Nat) : Int) := by
  have h := thetaCoeffAt_pair K ((n + 1 : Nat) : Int)
  have h' : -((n + 1 : Nat) : Int) - 1 = -(n : Int) - 2 := by
    push_cast
    ring
  rw [h'] at h
  exact h

#check thetaCoeffAt_neg_nat
#check thetaCoeffAt_neg_nat_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionNatActual
