import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaHalfIntInjActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrderConsumer

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

theorem halfInt_lt_iff {n m : Int} :
    halfInt n < halfInt m ↔ n < m := by
  constructor
  · intro h
    have hnle : n <= m := (halfInt_le_iff).1 (le_of_lt h)
    have hnot : ¬ m <= n := by
      intro hmn
      exact not_le_of_gt h ((halfInt_le_iff).2 hmn)
    omega
  · intro h
    have hnle : n <= m := le_of_lt h
    have hnot : ¬ m <= n := not_le_of_gt h
    have h1 : halfInt n <= halfInt m := (halfInt_le_iff).2 hnle
    have h2 : ¬ halfInt m <= halfInt n := by
      intro hmn
      exact hnot ((halfInt_le_iff).1 hmn)
    by_contra hlt
    exact h2 (le_of_not_gt hlt)

theorem halfInt_strictMono : StrictMono halfInt := by
  intro n m h
  exact (halfInt_lt_iff).mpr h

theorem halfInt_injective_consumer : Function.Injective halfInt :=
  LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual.halfInt_injective

theorem halfInt_eq_iff {n m : Int} :
    halfInt n = halfInt m ↔ n = m := by
  constructor
  · exact halfInt_injective_consumer
  · intro h; rw [h]

#check halfInt_strictMono
#check halfInt_injective_consumer
#check halfInt_eq_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrderConsumer
