import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrderEmbedding

theorem halfInt_le_iff {n m : Int} :
    halfInt n <= halfInt m ↔ n <= m := by
  unfold halfInt
  constructor
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by exact_mod_cast h
    linarith

theorem halfInt_injective_embedding : Function.Injective halfInt :=
  LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual.halfInt_injective

noncomputable def halfIntOrderEmbedding : Int ↪o Rat :=
  { toFun := fun n => (halfInt n : Rat)
    inj' := by
      intro n m h
      exact halfInt_injective_embedding (by simpa using h)
    map_rel_iff' := by
      intro n m
      exact halfInt_le_iff }

theorem halfIntOrderEmbedding_apply (n : Int) :
    halfIntOrderEmbedding n = halfInt n := rfl

#check halfIntOrderEmbedding
#check halfIntOrderEmbedding_apply

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrderEmbedding
