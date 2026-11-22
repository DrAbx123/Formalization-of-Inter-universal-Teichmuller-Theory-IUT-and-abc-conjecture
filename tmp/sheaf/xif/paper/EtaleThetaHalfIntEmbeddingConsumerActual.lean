import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingConsumerActual

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

theorem thetaQExponent_eq_halfInt (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaQExponent_strictMono_nonneg {a b : Int}
    (ha : 0 <= a) (hab : a < b) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent a <
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent b := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
  have ha' : (0 : Rat) <= (a : Rat) := by exact_mod_cast ha
  have hab' : (a : Rat) < (b : Rat) := by exact_mod_cast hab
  nlinarith

#check halfIntOrderEmbedding
#check thetaQExponent_eq_halfInt
#check thetaQExponent_strictMono_nonneg

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingConsumerActual
