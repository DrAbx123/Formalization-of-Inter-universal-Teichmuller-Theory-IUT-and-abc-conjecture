import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentEmbeddingConsumer

theorem thetaExponent_eq_halfInt_add (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) + (1 / 8 : Rat) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaExponent_eq_halfInt_add' (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n - (1 / 8 : Rat) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) := by
  rw [thetaExponent_eq_halfInt_add]
  ring

#check thetaExponent_eq_halfInt_add
#check thetaExponent_eq_halfInt_add'

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentEmbeddingConsumer
