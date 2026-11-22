import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreInvolutionTupleActual

theorem thetaExponent_pair_consumer (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

/-- The full theta involution package on q/X/U exponents. -/
theorem thetaInvolution_consumer (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n ∧
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-n - 1) =
      -LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent n ∧
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n :=
  ⟨LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent_neg_succ n,
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent_neg_succ n,
    thetaExponent_pair_consumer n⟩

#check thetaInvolution_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreInvolutionTupleActual
