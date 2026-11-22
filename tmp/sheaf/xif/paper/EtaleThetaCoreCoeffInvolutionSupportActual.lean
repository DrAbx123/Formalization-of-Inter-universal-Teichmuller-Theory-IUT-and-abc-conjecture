import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionSupportActual

universe u

theorem thetaCoeffAt_support_involution (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K (-n - 1)).support = (thetaCoeffAt K n).support := by
  rw [thetaCoeffAt_pair]

theorem thetaCoeffAt_coeff_involution (K : Type u) [Field K]
    (n : Int) (x : Int) :
    (thetaCoeffAt K (-n - 1)).coeff x = (thetaCoeffAt K n).coeff x := by
  rw [thetaCoeffAt_pair]

#check thetaCoeffAt_support_involution
#check thetaCoeffAt_coeff_involution

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionSupportActual
