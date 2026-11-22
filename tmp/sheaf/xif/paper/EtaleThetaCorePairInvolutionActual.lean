import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCorePairInvolutionActual

universe u

theorem thetaCoeffAt_pair_involution (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-(-n - 1) - 1) = thetaCoeffAt K n := by
  rw [show (-(-n - 1) - 1 : Int) = n by ring]

theorem thetaCoeffAt_pair_twice (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-(-n - 1) - 1) = thetaCoeffAt K n ∧
      thetaCoeffAt K (-n - 1) = thetaCoeffAt K n :=
  ⟨thetaCoeffAt_pair_involution K n, thetaCoeffAt_pair K n⟩

#check thetaCoeffAt_pair_involution
#check thetaCoeffAt_pair_twice

end LeanFormal.IUT.XiFPaper.EtaleThetaCorePairInvolutionActual
