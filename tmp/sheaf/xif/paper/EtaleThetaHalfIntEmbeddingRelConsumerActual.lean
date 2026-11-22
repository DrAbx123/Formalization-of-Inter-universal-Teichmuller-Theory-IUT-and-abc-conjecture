import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingRelConsumerActual

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

theorem halfIntOrderEmbedding_le_iff {n m : Int} :
    halfIntOrderEmbedding n <= halfIntOrderEmbedding m ↔ n <= m := by
  exact halfInt_le_iff

theorem halfInt_lt_iff {n m : Int} :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n <
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m ↔ n < m := by
  constructor
  · intro h
    have hnle : n <= m := halfInt_le_iff.1 (le_of_lt h)
    have hnot : ¬ m <= n := by
      intro hmn
      exact not_le_of_gt h (halfInt_le_iff.2 hmn)
    omega
  · intro h
    have h1 : LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n <=
        LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m :=
      halfInt_le_iff.2 (le_of_lt h)
    have h2 : ¬ LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m <=
        LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n := by
      intro hmn
      exact (not_le_of_gt h) (halfInt_le_iff.1 hmn)
    by_contra hlt
    exact h2 (le_of_not_gt hlt)

theorem halfIntOrderEmbedding_lt_iff {n m : Int} :
    halfIntOrderEmbedding n < halfIntOrderEmbedding m ↔ n < m := by
  exact halfInt_lt_iff

#check halfIntOrderEmbedding_le_iff
#check halfIntOrderEmbedding_lt_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingRelConsumerActual
