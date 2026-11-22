import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentEmbeddingRelConsumerActual

theorem halfInt_le_iff {n m : Int} :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n <=
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m ↔ n <= m := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  constructor
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by exact_mod_cast h
    linarith

noncomputable def halfIntOrderEmbedding : Int ↪o Rat :=
  { toFun := fun n => (LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n : Rat)
    inj' := by
      intro n m h
      apply LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual.halfInt_injective
      simpa using h
    map_rel_iff' := by
      intro n m
      exact halfInt_le_iff }

theorem thetaExponent_eq_embedding_add (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent n =
      halfIntOrderEmbedding (n * (n + 1)) + (1 / 8 : Rat) := by
  rw [show halfIntOrderEmbedding (n * (n + 1)) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) from rfl]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.thetaExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

#check thetaExponent_eq_embedding_add

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntThetaExponentEmbeddingRelConsumerActual
