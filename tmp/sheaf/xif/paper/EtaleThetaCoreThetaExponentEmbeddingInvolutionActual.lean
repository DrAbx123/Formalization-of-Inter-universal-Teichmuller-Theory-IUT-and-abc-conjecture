import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentEmbeddingInvolutionActual

theorem thetaExponent_eq_halfInt_add (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) + (1 / 8 : Rat) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaExponent_involution_embedding (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n ∧
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) + (1 / 8 : Rat) :=
  ⟨by
    unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
    rw [show (-n - 1 : Int) = -(n + 1) by ring]
    push_cast
    ring,
   thetaExponent_eq_halfInt_add n⟩

#check thetaExponent_eq_halfInt_add
#check thetaExponent_involution_embedding

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreThetaExponentEmbeddingInvolutionActual
