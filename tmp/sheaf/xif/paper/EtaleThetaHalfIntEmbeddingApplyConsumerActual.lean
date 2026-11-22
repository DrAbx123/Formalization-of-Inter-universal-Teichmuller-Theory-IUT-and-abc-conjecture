import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingApplyConsumerActual

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

theorem halfIntOrderEmbedding_apply (n : Int) :
    halfIntOrderEmbedding n = LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n := rfl

theorem halfIntOrderEmbedding_injective : Function.Injective halfIntOrderEmbedding :=
  halfIntOrderEmbedding.injective

theorem halfIntOrderEmbedding_strictMono : StrictMono halfIntOrderEmbedding :=
  halfIntOrderEmbedding.strictMono

#check halfIntOrderEmbedding_apply
#check halfIntOrderEmbedding_injective
#check halfIntOrderEmbedding_strictMono

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntEmbeddingApplyConsumerActual
