import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionTupleActual

universe u

theorem thetaExponent_pair_consumer (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

/-- The theta coefficient is invariant under the involution n -> -n-1,
    whose U-exponent is negated. -/
theorem thetaCoeffInvolution_consumer (K : Type u) [Field K] (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt K (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt K n ∧
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-n - 1) =
      -LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent n :=
  ⟨LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt_pair K n,
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent_neg_succ n⟩

#check thetaCoeffInvolution_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffInvolutionTupleActual
