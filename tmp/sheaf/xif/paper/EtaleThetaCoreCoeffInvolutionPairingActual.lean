import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionPairingActual

universe u

theorem thetaCoeffAt_pair_fwd (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n = thetaCoeffAt K (-n - 1) :=
  (thetaCoeffAt_pair K n).symm

theorem thetaCoeffAt_pair_double (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-(-n - 1) - 1) = thetaCoeffAt K (-n - 1) ∧
      thetaCoeffAt K (-n - 1) = thetaCoeffAt K n :=
  ⟨by rw [thetaCoeffAt_pair], thetaCoeffAt_pair K n⟩

#check thetaCoeffAt_pair_fwd
#check thetaCoeffAt_pair_double

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionPairingActual
