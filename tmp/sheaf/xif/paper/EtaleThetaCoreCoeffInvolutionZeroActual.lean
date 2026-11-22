import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionZeroActual

universe u

theorem thetaCoeffAt_neg_one (K : Type u) [Field K] :
    thetaCoeffAt K (-1) = thetaCoeffAt K 0 := by
  simpa using thetaCoeffAt_pair K 0

theorem thetaCoeffAt_neg_two (K : Type u) [Field K] :
    thetaCoeffAt K (-2) = thetaCoeffAt K 1 := by
  simpa using thetaCoeffAt_pair K 1

#check thetaCoeffAt_neg_one
theorem thetaCoeffAt_neg_three (K : Type u) [Field K] :
    thetaCoeffAt K (-3) = thetaCoeffAt K 2 := by
  simpa using thetaCoeffAt_pair K 2

#check thetaCoeffAt_neg_two
#check thetaCoeffAt_neg_three

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionZeroActual
