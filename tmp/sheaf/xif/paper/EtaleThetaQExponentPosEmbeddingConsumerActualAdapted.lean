import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaQExponentPosEmbeddingConsumerActualAdapted

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

theorem halfInt_lt_iff {n m : Int} :
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n <
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m ↔ n < m := by
  constructor
  · intro h
    have hnle : n <= m := halfInt_le_iff.1 (le_of_lt h)
    have hnot : ¬ m <= n := by
      intro hmn; exact not_le_of_gt h (halfInt_le_iff.2 hmn)
    omega
  · intro h
    have h1 : LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n <=
        LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m :=
      halfInt_le_iff.2 (le_of_lt h)
    have h2 : ¬ LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt m <=
        LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n := by
      intro hmn; exact (not_le_of_gt h) (halfInt_le_iff.1 hmn)
    by_contra hlt
    exact h2 (le_of_not_gt hlt)

noncomputable def halfIntOrderEmbedding : Int ↪o Rat :=
  { toFun := fun n => (LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt n : Rat)
    inj' := by
      intro n m h
      apply LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual.halfInt_injective
      simpa using h
    map_rel_iff' := by
      intro n m
      exact halfInt_le_iff }

theorem thetaQExponent_eq_embedding (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n =
      halfIntOrderEmbedding (n * (n + 1)) := by
  rw [show halfIntOrderEmbedding (n * (n + 1)) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) from rfl]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent
    LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
  push_cast
  ring

theorem thetaQExponent_pos_embedding {n : Int} (h : 0 < n) :
    0 < LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n := by
  have hprod : 0 < n * (n + 1) := by nlinarith
  rw [thetaQExponent_eq_embedding]
  have hemb : halfIntOrderEmbedding (n * (n + 1)) =
      LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt (n * (n + 1)) := rfl
  rw [hemb]
  have h0 : LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt 0 = 0 := by
    unfold LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt.halfInt
    norm_num
  rw [← h0]
  exact halfInt_lt_iff.mpr hprod

#check thetaQExponent_pos_embedding

end LeanFormal.IUT.XiFPaper.EtaleThetaQExponentPosEmbeddingConsumerActualAdapted
