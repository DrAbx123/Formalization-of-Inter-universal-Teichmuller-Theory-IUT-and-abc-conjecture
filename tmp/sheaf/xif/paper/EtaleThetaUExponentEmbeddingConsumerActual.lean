import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaUExponentEmbeddingConsumerActual

theorem thetaUExponent_eq_halfInt (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (2 * (2 * n + 1)) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaUExponent_eq_halfInt' (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (2 * (2 * n + 1)) =
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent n :=
  (thetaUExponent_eq_halfInt n).symm

#check thetaUExponent_eq_halfInt
#check thetaUExponent_eq_halfInt'

end LeanFormal.IUT.XiFPaper.EtaleThetaUExponentEmbeddingConsumerActual
